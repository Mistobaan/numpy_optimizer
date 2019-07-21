from abstract_peg import Eval_APEGNode, THETA_APEGNode
from abstract_peg import APEGNode, PHI_APEGNode
from abstract_peg import compute_apeg_from_source
from peg_nodes import BinOpNode, CompareNode, NumNode, ListNode, VariableNode, ComprehensionNode
from peg_nodes import StrNode, DictNode, TupleNode, UnaryOpNode, SetNode, FunctionCall, BoolOpNode, GeneratorExpNode
from peg_nodes import THETANode, PHINode, EvalNode, PassNode, Param, TemporaryNode, ListCompNode, SetCompNode
from peg_nodes import AttributeNode, SubscriptNode, SliceNode, ExtSliceNode, IndexNode, LambdaNode, NameConstantNode
from peg_nodes import IdentifierNode, NPArrayNode, SetSubscriptNode
import ast
import astor
import peg_nodes
from common_graph_funcs import get_nodes


class PEGBuilder(object):

    def __init__(self, apeg, function_def, line_durations, axiom_mode=False):

        self.function_def = function_def
        self.line_durations = line_durations
        self.ctx = {}
        self.current_id = 0
        self.axiom_mode = axiom_mode
        self.bindings = {}
        self.invariants = {}
        self.nodes = []
        self.eval_nodes = []
        self.phi_nodes = []
        self.function_line_offset = function_def.lineno - len(function_def.decorator_list) if not axiom_mode else None
        self.root = None

        self.translate_function(function_def, apeg)

    def compute_id(self):

        self.current_id += 1

        if self.axiom_mode:
            return - self.current_id

        return self.current_id

    @staticmethod
    def init_map(keys, f):

        values = list(map(f, keys))
        result = dict(zip(keys, values))
        return result

    def translate_function(self, function_def, apeg):

        if self.axiom_mode:
            m = {}
        else:
            function_args = [each.arg for each in function_def.args.args]
            m = self.init_map(function_args, lambda arg: Param(self.compute_id(), arg))
        root = apeg.apeg_root

        self.ctx = self.visit_apeg_node(root, [], m, loop_depth=0)

        self.filter_redundant_nodes()
        self.remove_duplicates()
        self.compute_loop_variance_indices()

    def filter_redundant_nodes(self):

        self.add_predecessors(self.ctx)

        changed_phi_nodes = True
        changed_theta_nodes = True

        while changed_phi_nodes or changed_theta_nodes:
            changed_theta_nodes = self.remove_selfloops()
            changed_phi_nodes = self.remove_phi_nodes_with_equal_cases()

        if self.axiom_mode:

            nodes = []
            for key in self.ctx.keys():
                nodes += get_nodes(self.ctx[key])

            self.nodes = list(set(nodes))

        else:
            self.root = self.ctx['retvar']
            self.nodes = get_nodes(self.root)

    def compute_loop_condition(self, loop_header_stmt):

        assert (isinstance(loop_header_stmt, ast.For) or isinstance(loop_header_stmt, ast.While))

        if isinstance(loop_header_stmt, ast.While):
            return loop_header_stmt.test

        if isinstance(loop_header_stmt, ast.For):
            iterator = loop_header_stmt.iter
            var = loop_header_stmt.target
            loop_condition = ast.Compare(left=var, ops=[ast.In()], comparators=[iterator])
            loop_condition.lineno = loop_header_stmt.lineno
            return loop_condition

    def is_loop_header(self, node):

        if len(node.statements) == 0:
            return False

        if isinstance(node.statements[0], ast.For) or isinstance(node.statements[0], ast.While):
            return True

        return False

    def replace_node(self, old_node, new_node):

        for pred in old_node.predecessors:
            indices = [i for i in range(len(pred.children)) if pred.children[i].id == old_node.id]

            for i in indices:
                pred.children[i] = new_node

            new_node.predecessors.append(pred)

        if old_node in new_node.predecessors:
            new_node.predecessors.remove(old_node)

        for key in self.ctx.keys():
            if self.ctx[key].id == old_node.id:
                self.ctx[key] = new_node

    def visit_apeg_node(self, node, visited, ctx, loop_depth):

        if node in visited:
            return ctx

        visited.append(node)

        if isinstance(node, PHI_APEGNode):

            cond = node.condition_node().boolean_expression()
            t = node.true_node()
            f = node.false_node()

            t_visited = list.copy(visited)
            f_visited = list.copy(visited)
            t_successors = self.nodes_reachable_from(t, t_visited)
            f_successors = self.nodes_reachable_from(f, f_visited)

            same_successors = [succ for succ in t_successors if succ in f_successors]

            if len(same_successors) > 0:
                ctx = self.visit_apeg_node(same_successors[0], visited, ctx, loop_depth)

            t_ctx = self.visit_apeg_node(t, visited, ctx, loop_depth)
            f_ctx = self.visit_apeg_node(f, visited, ctx, loop_depth)

            ctx = self.PHI(self.TE(cond, ctx), t_ctx, f_ctx)

            for key in ctx.keys():
                if isinstance(ctx[key], PHINode):
                    self.phi_nodes.append(ctx[key])
                    self.nodes.append(ctx[key])

            return ctx

        if isinstance(node, Eval_APEGNode):

            loop_header = node.theta_node()
            loop_cond = self.compute_loop_condition(loop_header.statements[0])
            break_condition = ast.UnaryOp(op=ast.Not(),
                                          operand=loop_cond)

            break_condition.lineno = loop_cond.lineno

            loop_header_ctx = self.visit_apeg_node(loop_header, visited, ctx, loop_depth)
            pass_node = PassNode(self.compute_id(), [self.TE(break_condition, loop_header_ctx)])

            if not self.axiom_mode:
                # pass node cost is set to loop header line duration
                try:
                    cost = self.line_durations[break_condition.lineno + self.function_line_offset]
                except:
                    cost = 1

                pass_node.cost = cost

            eval_ctx = self.EVAL(loop_header_ctx, pass_node, loop_depth)

            for key in eval_ctx.keys():
                self.eval_nodes.append(eval_ctx[key])

            return eval_ctx

        if isinstance(node, THETA_APEGNode):

            initial = node.initial_node()
            iteration = node.iteration_node()

            initial_ctx = self.visit_apeg_node(initial, visited, ctx, loop_depth)
            variables = initial_ctx.keys()

            ctx_tmp = self.init_map(variables, lambda k: TemporaryNode(self.compute_id(), k))
            ctx_prim = self.visit_apeg_node(iteration, visited, ctx_tmp, loop_depth + 1)
            ctx_theta = self.THETA(initial_ctx, ctx_prim, loop_depth)
            ctx_theta_fixed = self.init_map(variables, lambda k: self.fixpoint_temps(ctx_theta, k, loop_depth))

            return ctx_theta_fixed

        assert (isinstance(node, APEGNode))

        if self.is_loop_header(node):
            theta_ctx = self.visit_apeg_node(node.children[0], visited, ctx, loop_depth)

            return theta_ctx

        for child in node.children:
            ctx = self.visit_apeg_node(child, visited, ctx, loop_depth)

        ctx = self.TS(node.statements, ctx, loop_depth)

        return ctx

    # translate statement function
    def TS(self, stmt, ctx, loop_depth):

        new_ctx = dict.copy(ctx)

        if isinstance(stmt, list):
            if len(stmt) > 1:
                return self.TS(stmt[1:], self.TS(stmt[0], new_ctx, loop_depth), loop_depth)

            elif len(stmt) == 1:
                return self.TS(stmt[0], new_ctx, loop_depth)

            else:
                return new_ctx

        if isinstance(stmt, ast.Assign):

            if self.axiom_mode:
                target = stmt.targets[0]

                # setting node attribute in axiom mode
                if isinstance(target, ast.Attribute) and target.value.id in new_ctx.keys():

                    # setting other node's attribute value to current node attribute
                    if isinstance(stmt.value, ast.Attribute):
                        expression = stmt.value
                        assert (isinstance(expression.value, ast.Name))
                        value = expression.value.id
                        value_to_set = getattr(new_ctx[value], expression.attr)

                    # setting node's attribute to literal value
                    else:
                        value_to_set = ast.literal_eval(astor.to_source(stmt.value))

                    node = new_ctx[target.value.id]
                    setattr(node, target.attr, value_to_set)
                    return new_ctx

                # condition in axiom
                if isinstance(target, ast.Name) and target.id.startswith('condition'):
                    self.process_axiom_condition(stmt, new_ctx)

            # non-axiom case
            for var in stmt.targets:
                expression = stmt.value

                if isinstance(var, ast.Name):
                    new_ctx[var.id] = self.TE(expression, new_ctx)

                elif isinstance(var, ast.Subscript):

                    collection = var.value

                    assert(isinstance(collection, ast.Name))
                    slice = self.TE(var.slice, new_ctx)
                    value = self.TE(expression, new_ctx)

                    children = [new_ctx[collection.id], slice, value]
                    new_ctx[collection.id] = SetSubscriptNode(self.compute_id(), children)


                return new_ctx

        if isinstance(stmt, ast.AugAssign):
            var = stmt.target
            operator = ast.BinOp(left=var, op=stmt.op, right=stmt.value)
            new_ctx[var.id] = self.TE(operator, new_ctx)

            return new_ctx

        if isinstance(stmt, ast.AnnAssign):

            var = stmt.target
            annot = stmt.annotation.id
            value = stmt.value

            if self.axiom_mode:

                # binded node case
                if var.id.startswith('_'):

                    new_ctx[var.id] = getattr(peg_nodes, annot)(self.compute_id())
                    binded_node = new_ctx[var.id]
                    self.bindings[binded_node.id] = binded_node

                # new node to instantiate case
                else:

                    new_ctx[var.id] = getattr(peg_nodes, annot)(self.compute_id())

            else:
                new_ctx[var.id] = self.TE(value, new_ctx)

            return new_ctx

        if isinstance(stmt, ast.Return):

            new_ctx['retvar'] = self.TE(stmt.value, new_ctx)

            return new_ctx

        if isinstance(stmt, ast.Pass):
            return new_ctx

        if isinstance(stmt, ast.While):
            return new_ctx

        if isinstance(stmt, ast.For):
            return new_ctx

        raise Exception('Currently unsuported type: ' + str(type(stmt)))

    # translate expression function
    def TE(self, expression, ctx):

        # default cost
        cost = 1

        if not self.axiom_mode:

            try:
                lineno = expression.lineno + self.function_line_offset
                cost = self.line_durations[lineno]

            except:
                print('Current line duration is unknown.')


        if isinstance(expression, ast.Name):

            if not expression.id in ctx.keys():

                node = IdentifierNode(self.compute_id(), expression.id)

            elif isinstance(ctx[expression.id], TemporaryNode):
                tmp_node = ctx[expression.id]
                node = TemporaryNode(self.compute_id(), tmp_node.name)

            else:
                node = ctx[expression.id]

        elif isinstance(expression, ast.Num):

            node = NumNode(self.compute_id(), expression)


        elif isinstance(expression, ast.Str):

            node = StrNode(self.compute_id(), expression)

        elif isinstance(expression, ast.NameConstant):

            node = NameConstantNode(self.compute_id(), expression)

        elif isinstance(expression, ast.List):

            elements = list(map(lambda e: self.TE(e, ctx), expression.elts))
            node = ListNode(self.compute_id(), elements)

        elif isinstance(expression, ast.Set):

            elements = list(map(lambda e: self.TE(e, ctx), expression.elts))
            node = SetNode(self.compute_id(), elements)

        elif isinstance(expression, ast.Tuple):

            elements = list(map(lambda e: self.TE(e, ctx), expression.elts))
            node = TupleNode(self.compute_id(), elements)

        elif isinstance(expression, ast.Dict):

            keys = list(map(lambda k: self.TE(k, ctx), expression.keys))
            values = list(map(lambda v: self.TE(v, ctx), expression.values))
            node = DictNode(self.compute_id(), [keys] + [values])

        elif isinstance(expression, ast.BinOp):

            op = expression.op
            args = [self.TE(expression.left, ctx), self.TE(expression.right, ctx)]
            node = BinOpNode(self.compute_id(), op, args)
            node.cost = cost

        elif isinstance(expression, ast.BoolOp):

            op = expression.op
            args = [self.TE(operand, ctx) for operand in expression.values]
            node = BoolOpNode(self.compute_id(), op, args)
            node.cost = cost

        elif isinstance(expression, ast.Compare):

            head = self.TE(expression.left, ctx)
            ops = expression.ops
            tail = [self.TE(operand, ctx) for operand in expression.comparators]
            node = CompareNode(self.compute_id(), ops, [head] + tail)
            node.cost = cost

        elif isinstance(expression, ast.UnaryOp):

            node = UnaryOpNode(self.compute_id(), expression.op, [self.TE(expression.operand, ctx)])
            self.nodes.append(node)
            node.cost = cost

        elif isinstance(expression, ast.Call):

            args = list(map(lambda a: self.TE(a, ctx), expression.args))

            # adding children to nodes created in axiom mode
            if self.axiom_mode and isinstance(expression.func, ast.Name) and expression.func.id in ctx.keys():

                name = expression.func
                ctx[name.id].children = args
                node = ctx[name.id]

            # creating nparray node
            elif isinstance(expression.func, ast.Attribute) and isinstance(expression.func.value, ast.Name) and \
                expression.func.value.id == 'np' and expression.func.attr == 'array':

                node = NPArrayNode(self.compute_id(), args)

            else:

                func = self.TE(expression.func, ctx)
                node = FunctionCall(self.compute_id(), [func] + args)

            node.cost = cost


        elif isinstance(expression, ast.Lambda):

            args = list(map(lambda a: self.TE(a, ctx), expression.args.args))

            # lambda function has new ctx
            new_ctx = ctx.copy()

            for arg in args:
                new_ctx[arg.name] = arg

            body = self.TE(expression.body, new_ctx)
            node = LambdaNode(self.compute_id(), args + [body])

        elif isinstance(expression, ast.arg):

            node = VariableNode(self.compute_id(), expression.arg)

        elif isinstance(expression, ast.Attribute):

            value = self.TE(expression.value, ctx)
            node = AttributeNode(self.compute_id(), expression.attr, [value])

        elif isinstance(expression, ast.Subscript):

            value = self.TE(expression.value, ctx)
            slice = self.TE(expression.slice, ctx)
            node = SubscriptNode(self.compute_id(), [value, slice])

        elif isinstance(expression, ast.Index):

            value = self.TE(expression.value, ctx)
            node = IndexNode(self.compute_id(), [value])

        elif isinstance(expression, ast.Slice):

            none_expression = ast.NameConstant(None)

            lower = self.TE(expression.lower, ctx) if expression.lower != None else \
                NameConstantNode(self.compute_id(), none_expression)

            upper = self.TE(expression.upper, ctx) if expression.upper != None else \
                NameConstantNode(self.compute_id(), none_expression)

            step = self.TE(expression.step, ctx) if expression.step != None else \
                NameConstantNode(self.compute_id(), none_expression)

            node = SliceNode(self.compute_id(), [lower, upper, step])

        elif isinstance(expression, ast.ExtSlice):

            dims = [self.TE(dim, ctx) for dim in expression.dims]
            node = ExtSliceNode(self.compute_id(), dims)

        elif isinstance(expression, ast.comprehension):

            if isinstance(expression.target, ast.Name):
                target = VariableNode(self.compute_id(), expression.target.id)
                ctx[target.name] = target

            else:
                target_vars = [VariableNode(self.compute_id(), arg.id) for arg in expression.target]
                for var in target_vars:
                    ctx[var.name] = var

                target = TupleNode(self.compute_id(), target_vars)

            iter = self.TE(expression.iter, ctx)
            ifs = [self.TE(test, ctx) for test in expression.ifs]

            node = ComprehensionNode(self.compute_id(), [target, iter] + ifs)


        elif isinstance(expression, ast.ListComp):

            generators = [self.TE(gen, ctx) for gen in expression.generators]
            elt = self.TE(expression.elt, ctx)
            node = ListCompNode(self.compute_id(), [elt] + generators)


        elif isinstance(expression, ast.SetComp):

            generators = [self.TE(gen, ctx) for gen in expression.generators]
            elt = self.TE(expression.elt, ctx)
            node = SetCompNode(self.compute_id(), [elt] + generators)


        elif isinstance(expression, ast.GeneratorExp):

            generators = [self.TE(gen, ctx) for gen in expression.generators]
            elt = self.TE(expression.elt, ctx)
            node = GeneratorExpNode(self.compute_id(), [elt] + generators)


        elif isinstance(expression, ast.DictComp):

            generators = [self.TE(gen, ctx) for gen in expression.generators]
            key = self.TE(expression.key, ctx)
            value = self.TE(expression.value, ctx)
            node = ListCompNode(self.compute_id(), [key, value] + generators)

        else:
            raise Exception('Currently unsuported type: ' + str(type(expression)))

        self.nodes.append(node)
        return node

    def combine(self, ctx1, ctx2, f):

        key_intersection = list(ctx1.keys() & ctx2.keys())
        mapping_function = lambda k: f(ctx1[k], ctx2[k], k)

        return self.init_map(key_intersection, mapping_function)

    def PHI(self, node, ctx1, ctx2):

        new_ctx1 = dict.copy(ctx1)
        new_ctx2 = dict.copy(ctx2)

        return self.combine(new_ctx1, new_ctx2,
                            lambda t, f, _: t if t.id == f.id else PHINode(self.compute_id(), [node, t, f]))

    def THETA(self, ctx1, ctx2, loop_depth):

        new_ctx1 = dict.copy(ctx1)
        new_ctx2 = dict.copy(ctx2)

        return self.combine(new_ctx1, new_ctx2,
                            lambda b, n, k: THETANode(self.compute_id(), [b, n], loop_depth,
                                                                          k[1:] if k.startswith('_') else k))

    def EVAL(self, ctx, node, loop_depth):

        new_ctx = dict.copy(ctx)

        return self.init_map(new_ctx.keys(),
                             lambda k: EvalNode(self.compute_id(), [new_ctx[k], node], loop_depth))

    def nodes_reachable_from(self, node, visited):

        successors = []
        self.nodes_reachable_from_helper(node, visited, successors)

        return successors

    def nodes_reachable_from_helper(self, node, visited, successors):

        if node in visited:
            return

        visited.append(node)
        successors.append(node)

        for child in node.children:
            if child != None:
                self.nodes_reachable_from_helper(child, visited, successors)

    def fixpoint_temps_helper(self, ctx, node, loop_depth, visited):

        if node.id in visited:
            return

        visited.append(node.id)

        for i in range(len(node.children)):
            self.fixpoint_temps_helper(ctx, node.children[i], loop_depth, visited)

            if isinstance(node.children[i], TemporaryNode):

                # pass theta node's initial child at current loop depth
                if not (isinstance(node, THETANode) and node.loop_depth == loop_depth and i == 0):
                    original_var_name = node.children[i].name
                    node.children[i] = ctx[original_var_name]


    def fixpoint_temps(self, ctx, key, loop_depth):

        node = ctx[key]

        assert (isinstance(ctx[key], THETANode))

        root = ctx[key].children[1]

        self.fixpoint_temps_helper(ctx, root, loop_depth, [])

        if isinstance(node.children[1], TemporaryNode):
            original_var_name = node.children[1].name
            node.children[1] = ctx[original_var_name]

        return ctx[key]


    def add_predecessors(self, ctx):

        for key in ctx.keys():
            self.add_predecessors_helper(ctx[key], [])

    def add_predecessors_helper(self, root, visited):

        if root.id in visited:
            return

        visited.append(root.id)

        for child in root.children:
            child.predecessors.append(root)

            self.add_predecessors_helper(child, visited)

    def remove_phi_nodes_with_equal_cases(self):

        nodes_to_remove = []

        for phi_node in self.phi_nodes:

            if phi_node.t().id == phi_node.f().id:
                self.replace_node(phi_node, phi_node.t())
                nodes_to_remove.append(phi_node)

        for key in self.ctx.keys():

            if isinstance(self.ctx[key], PHINode):

                phi_node = self.ctx[key]

                if len(phi_node.children) == 3 and phi_node.t().id == phi_node.f().id:
                    self.ctx[key] = phi_node.t()
                    nodes_to_remove.append(phi_node)

        for node in nodes_to_remove:
            if node in self.phi_nodes:
                self.phi_nodes.remove(node)

        return len(nodes_to_remove) != 0

    def remove_selfloops(self):

        self.eval_nodes = sorted(self.eval_nodes, key=lambda e: e.loop_depth, reverse=True)
        nodes_to_remove = []

        for eval_node in self.eval_nodes:

            theta_node = eval_node.children[0]

            if len(theta_node.children) < 2:
                continue

            theta_init = theta_node.children[0]
            theta_iter = theta_node.children[1]

            if theta_node.id == theta_iter.id:
                self.replace_node(eval_node, theta_init)
                nodes_to_remove.append(eval_node)
                self.replace_node(theta_node, theta_init)

        for key in self.ctx.keys():

            if isinstance(self.ctx[key], EvalNode):

                theta_node = self.ctx[key].children[0]

                if not isinstance(theta_node, THETANode):

                    if self.axiom_mode and (key == 'lhs' or key == 'rhs'):
                        continue

                    self.ctx[key] = self.ctx[key].children[0]
                    nodes_to_remove.append(self.ctx[key])

                if len(theta_node.children) == 2 and theta_node.children[1].id == theta_node.id:
                    self.ctx[key] = theta_node.children[0]
                    nodes_to_remove.append(self.ctx[key])

        for node in nodes_to_remove:
            if node in self.eval_nodes:
                self.eval_nodes.remove(node)

        # changes happened, so function should be called again
        return len(nodes_to_remove) != 0

    def remove_duplicates(self):

        for node in self.nodes:
            same_nodes = list(filter(lambda elem: node.same(elem), self.nodes))
            if len(same_nodes) > 1 and node != same_nodes[0]:
                self.replace_node(node, same_nodes[0])

    def compute_loop_variance_indices(self):

        visited = []

        for key in self.ctx.keys():

            if isinstance(self.ctx[key], THETANode):
                self.ctx[key].loop_variance_indices.add(self.ctx[key].loop_depth)

            self.compute_loop_variance_indices_helper(self.ctx[key], visited)

    def compute_loop_variance_indices_helper(self, root, visited):

        if root.id in visited:
            return

        visited.append(root.id)

        for child in root.children:
            if isinstance(child, THETANode):
                child.loop_variance_indices.add(child.loop_depth)
            self.compute_loop_variance_indices_helper(child, visited)

        if isinstance(root, EvalNode):
            pass_node = root.children[1]
            root.loop_variance_indices = root.loop_variance_indices.union(pass_node.loop_variance_indices)

        if not isinstance(root, PassNode):

            for child in root.children:
                root.loop_variance_indices = root.loop_variance_indices.union(child.loop_variance_indices)

    def process_axiom_condition(self, stmt, ctx):

        assert self.axiom_mode
        assert isinstance(stmt, ast.Assign) and isinstance(stmt.targets[0], ast.Name)
        assert stmt.targets[0].id.startswith('condition')

        value = stmt.value
        if isinstance(value, ast.Call) and isinstance(value.func, ast.Name):
            if value.func.id == 'invariant':

                inv_node = ctx[value.args[0].id]
                loop_node = ctx[value.args[1].id]
                self.invariants[inv_node.id] = loop_node.id


def compute_peg(func_def, line_durations):

    apeg, function_def = compute_apeg_from_source(astor.to_source(func_def), func_def.name)
    peg = PEGBuilder(apeg, func_def, line_durations)

    return peg


def compute_axiom_peg(src, name):

    apeg, function_def = compute_apeg_from_source(src, name)
    peg = PEGBuilder(apeg, function_def, None, axiom_mode=True)

    return peg

