from abstract_peg import Eval_APEGNode, Pass_APEGNode, THETA_APEGNode, Condition_APEGNode, True_APEGNode, False_APEGNode
from abstract_peg import APEGNode, PHI_APEGNode
from abstract_peg import compute_apeg
from peg_nodes import BinOpNode, CompareNode, BytesNode, NumericNode, ListNode, VariableNode, ComprehensionNode
from peg_nodes import StringNode, DictNode, TupleNode, UnaryOpNode, SetNode, FunctionCall, BoolOpNode, GeneratorExpNode
from peg_nodes import THETANode, PHINode, EvalNode, PassNode, Param, TemporaryNode, ListCompNode, SetCompNode
from peg_nodes import AttributeNode, SubscriptNode, SliceNode, ExtSliceNode, IndexNode, LambdaNode
import ast


def replace_node(old_node, new_node):

    for pred in old_node.predecessors:

        indices = [i for i in range(len(pred.children)) if pred.children[i].id == old_node.id]

        for i in indices:
            pred.children[i] = new_node

        new_node.predecessors.append(pred)

    if old_node in new_node.predecessors:
        new_node.predecessors.remove(old_node)


class PEGBuilder(object):

    def __init__(self, apeg, function_def):

        self.function_def = function_def
        self.nodes_map = {}
        self.apeg = apeg
        self.ctx = {}
        self.current_id = 0

        self.eval_nodes = []

        self.root = self.translateFunction(self.function_def)

    def compute_id(self):

        self.current_id += 1
        return self.current_id

    @staticmethod
    def init_map(keys, f):

        values = list(map(f, keys))
        result = dict(zip(keys, values))
        return result

    def translateFunction(self, function_def):

        function_args = [each.arg for each in function_def.args.args]
        m = self.init_map(function_args, lambda arg: Param(self.compute_id(), arg))
        root = self.apeg.apeg_root

        self.ctx = self.visit_apeg_node(root, [], m, loop_depth=0)
        self.add_predecessors(self.ctx)

        self.eval_nodes = sorted(self.eval_nodes, key=lambda e: e.loop_depth, reverse=True)

        self.remove_selfloops(self.eval_nodes)

        if isinstance(self.ctx['retvar'], EvalNode):

            theta_node = self.ctx['retvar'].children[0]

            # check this condition!
            if not isinstance(theta_node, THETANode):
                self.ctx['retvar'] = self.ctx['retvar'].children[0]

            if theta_node.children[1].id == theta_node.id:
                self.ctx['retvar'] = theta_node.children[0]

        return self.ctx['retvar']

    def compute_loop_condition(self, loop_header_stmt):

        assert (isinstance(loop_header_stmt, ast.For) or isinstance(loop_header_stmt, ast.While))

        if isinstance(loop_header_stmt, ast.While):
            return loop_header_stmt.test

        if isinstance(loop_header_stmt, ast.For):
            iterator = loop_header_stmt.iter
            var = loop_header_stmt.target
            return ast.Compare(left=var, ops=[ast.In()], comparators=[iterator])

    def extract_forloop_init_and_iter_stmt(self, forloop_stmt):

        assert (isinstance(forloop_stmt, ast.For))

        loop_var = forloop_stmt.target
        iterator = forloop_stmt.iter

        call = ast.Call(func=ast.Name(id='iter', ctx=ast.Load()), args=[iterator], keywords=[])
        loop_var_assign = ast.Assign(targets=[loop_var], value=call)

        next_expression = ast.Call(func=ast.Name(id='next', ctx=ast.Load()), args=[loop_var], keywords=[])
        next_stmt = ast.Assign(targets=[loop_var], value=next_expression)

        return loop_var_assign, next_stmt

    def is_loop_header(self, node):

        if len(node.statements) == 0:
            return False

        if isinstance(node.statements[0], ast.For) or isinstance(node.statements[0], ast.While):
            return True

        return False

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

            return ctx

        if isinstance(node, Eval_APEGNode):

            loop_header = node.theta_node()
            break_condition = ast.UnaryOp(op=ast.Not(),
                                          operand=self.compute_loop_condition(loop_header.statements[0]))

            if (isinstance(loop_header.statements[0], ast.For)):

                theta_node = loop_header.children[0]
                init_node = theta_node.children[0]
                iter_node = theta_node.children[1]

                init_stmt, iter_stmt = self.extract_forloop_init_and_iter_stmt(loop_header.statements[0])

                if isinstance(init_node, APEGNode) and not self.is_loop_header(init_node):
                    init_node.statements = [init_stmt] + init_node.statements
                else:
                    ctx = self.TS(init_stmt, ctx, loop_depth)

                if isinstance(iter_node, APEGNode) and not self.is_loop_header(iter_node):
                    iter_node.statements.append(iter_stmt)
                else:
                    new_node = APEGNode(self.apeg.compute_id(), children=[iter_node], statements=[iter_stmt])
                    theta_node.children[1] = new_node


            loop_header_ctx = self.visit_apeg_node(loop_header, visited, ctx, loop_depth)

            eval_ctx = self.EVAL(loop_header_ctx,
                                 PassNode(self.compute_id(), self.TE(break_condition, loop_header_ctx)), loop_depth)

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

            for var in stmt.targets:
                expression = stmt.value
                new_ctx[var.id] = self.TE(expression, new_ctx)

                return new_ctx

        if isinstance(stmt, ast.AugAssign):
            var = stmt.target
            operator = ast.BinOp(left=var, op=stmt.op, right=stmt.value)
            new_ctx[var.id] = self.TE(operator, new_ctx)

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

        print('UNRECOGNIZED TYPE:', type(stmt))

    def TE(self, expression, ctx):

        new_ctx = dict.copy(ctx)

        if isinstance(expression, ast.Name):

            if not expression.id in new_ctx.keys():
                return VariableNode(self.compute_id(), expression.id)

            if isinstance(new_ctx[expression.id], TemporaryNode):
                tmp_node = new_ctx[expression.id]
                return TemporaryNode(self.compute_id(), tmp_node.name)

            node = new_ctx[expression.id]
            return node

        if isinstance(expression, ast.Num):
            node = NumericNode(self.compute_id(), expression)

            return node

        if isinstance(expression, ast.Str):
            node = StringNode(self.compute_id(), expression)

            return node

        if isinstance(expression, ast.NameConstant):
            node = NameConstantNode(self.compute_id(), expression)

            return node

        if isinstance(expression, ast.List):
            elements = list(map(lambda e: self.TE(e, new_ctx), expression.elts))
            node = ListNode(self.compute_id(), elements)

            return node

        if isinstance(expression, ast.Set):
            elements = list(map(lambda e: self.TE(e, new_ctx), expression.elts))
            node = SetNode(self.compute_id(), elements)

            return node

        if isinstance(expression, ast.Tuple):
            elements = list(map(lambda e: self.TE(e, new_ctx), expression.elts))
            node = TupleNode(self.compute_id(), elements)

            return node

        if isinstance(expression, ast.Dict):
            keys = list(map(lambda k: self.TE(k, new_ctx), expression.keys))
            values = list(map(lambda v: self.TE(v, new_ctx), expression.values))

            node = DictNode(self.compute_id(), keys, values)

            return node

        if isinstance(expression, ast.BinOp):
            op = expression.op
            args = [self.TE(expression.left, new_ctx), self.TE(expression.right, new_ctx)]
            node = BinOpNode(self.compute_id(), op, args)

            return node

        if isinstance(expression, ast.BoolOp):
            op = expression.op
            args = [self.TE(operand, new_ctx) for operand in expression.values]
            node = BoolOpNode(self.compute_id(), op, args)

            return node

        if isinstance(expression, ast.Compare):
            head = self.TE(expression.left, new_ctx)
            ops = expression.ops
            tail = [self.TE(operand, new_ctx) for operand in expression.comparators]
            node = CompareNode(self.compute_id(), head, ops, tail)

            return node

        if isinstance(expression, ast.UnaryOp):
            node = UnaryOpNode(self.compute_id(), expression.op, self.TE(expression.operand, new_ctx))
            return node

        if isinstance(expression, ast.Call):

            name = self.TE(expression.func, new_ctx)
            args = list(map(lambda a: self.TE(a, new_ctx), expression.args))

            node = FunctionCall(self.compute_id(), name, args)

            return node

        if isinstance(expression, ast.Lambda):

            args = list(map(lambda a: self.TE(a, new_ctx), expression.args.args))

            for arg in args:
                new_ctx[arg.name] = arg

            body = self.TE(expression.body, new_ctx)

            node = LambdaNode(self.compute_id(), args, body)

            return node

        if isinstance(expression, ast.arg):

            return VariableNode(self.compute_id(), expression.arg)


        if isinstance(expression, ast.Attribute):

            value = self.TE(expression.value, new_ctx)

            node = AttributeNode(self.compute_id(), value, expression.attr)

            return node

        if isinstance(expression, ast.Subscript):

            value = self.TE(expression.value, new_ctx)
            slice = self.TE(expression.slice, new_ctx)

            node = SubscriptNode(self.compute_id(), value, slice)

            return node

        if isinstance(expression, ast.Index):

            value = self.TE(expression.value, new_ctx)

            node = IndexNode(self.compute_id(), value)

            return node


        if isinstance(expression, ast.Slice):

            none_expression = ast.NameConstant(None)

            lower = self.TE(expression.lower, new_ctx) if expression.lower != None else \
                NameConstantNode(self.compute_id(), none_expression)

            upper = self.TE(expression.upper, new_ctx) if expression.upper != None else \
                NameConstantNode(self.compute_id(), none_expression)

            step = self.TE(expression.step, new_ctx) if expression.step != None else \
                NameConstantNode(self.compute_id(), none_expression)

            node = SliceNode(self.compute_id(), lower, upper, step)

            return node


        if isinstance(expression, ast.ExtSlice):

            dims = [self.TE(dim, new_ctx) for dim in expression.dims]

            node = ExtSliceNode(self.compute_id(), dims)

            return node


        if isinstance(expression, ast.comprehension):

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
            ifs_list = ListNode(self.compute_id(), ifs)

            node = ComprehensionNode(self.compute_id(), target, iter, ifs_list)

            return node


        if isinstance(expression, ast.ListComp):

            generators = [self.TE(gen, ctx) for gen in expression.generators]
            elt = self.TE(expression.elt, ctx)


            node = ListCompNode(self.compute_id(), elt, generators)

            return node

        if isinstance(expression, ast.SetComp):

            generators = [self.TE(gen, ctx) for gen in expression.generators]
            elt = self.TE(expression.elt, ctx)

            node = SetCompNode(self.compute_id(), elt, generators)

            return node

        if isinstance(expression, ast.GeneratorExp):

            generators = [self.TE(gen, ctx) for gen in expression.generators]
            elt = self.TE(expression.elt, ctx)

            node = GeneratorExpNode(self.compute_id(), elt, generators)

            return node

        if isinstance(expression, ast.DictComp):

            generators = [self.TE(gen, ctx) for gen in expression.generators]
            key = self.TE(expression.key, ctx)
            value = self.TE(expression.value, ctx)

            node = ListCompNode(self.compute_id(), key, value, generators)

            return node


        print('UNRECOGNIZED TYPE expression:', type(expression))

    def combine(self, ctx1, ctx2, f):

        key_intersection = list(ctx1.keys() & ctx2.keys())
        mapping_function = lambda k: f(ctx1[k], ctx2[k], k)

        return self.init_map(key_intersection, mapping_function)

    def PHI(self, node, ctx1, ctx2):

        new_ctx1 = dict.copy(ctx1)
        new_ctx2 = dict.copy(ctx2)

        return self.combine(ctx1, ctx2, lambda t, f, _: t if t == f else PHINode(self.compute_id(), node, t, f))

    def THETA(self, ctx1, ctx2, loop_depth):

        new_ctx1 = dict.copy(ctx1)
        new_ctx2 = dict.copy(ctx2)

        return self.combine(ctx1, ctx2, lambda b, n, k: THETANode(self.compute_id(), b, n, loop_depth, k))

    def EVAL(self, ctx, node, loop_depth):

        new_ctx = dict.copy(ctx)

        return self.init_map(new_ctx.keys(),
                             lambda k: EvalNode(self.compute_id(), new_ctx[k], node, loop_depth))

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
            if root not in child.predecessors:
                child.predecessors.append(root)

            self.add_predecessors_helper(child, visited)

    def remove_selfloops(self, eval_nodes):

        for eval_node in eval_nodes:

            theta_node = eval_node.children[0]
            theta_init = theta_node.children[0]
            theta_iter = theta_node.children[1]

            if theta_node.id == theta_iter.id:
                replace_node(eval_node, theta_init)
                replace_node(theta_node, theta_init)



import graphviz


def fill_graph_helper(root, g, visited):
    if root in visited:
        return

    visited.append(root)

    g.node(str(root.id), label=str(root))

    for i in range(len(root.children)):

        if isinstance(root, PHINode):
            if i == 0:
                g.edge(str(root.id), str(root.children[i].id), label='cond')
            elif i == 1:
                g.edge(str(root.id), str(root.children[i].id), label='t')
            else:
                g.edge(str(root.id), str(root.children[i].id), label='f')

        elif isinstance(root, THETANode):
            if i == 0:
                g.edge(str(root.id), str(root.children[i].id), label='init')
            elif i == 1:
                g.edge(str(root.id), str(root.children[i].id), label='iter')

        elif isinstance(root, ListNode) or isinstance(root, TupleNode) or isinstance(root, ExtSliceNode):
            g.edge(str(root.id), str(root.children[i].id), label=str(i))

        elif isinstance(root, DictNode):
            if i in range(0, int(len(root.children) / 2)):
                g.edge(str(root.id), str(root.children[i].id), label='k_' + str(i))
            else:
                g.edge(str(root.id), str(root.children[i].id), label='v_' + str(i - int(len(root.children) / 2)))


        elif isinstance(root, SliceNode):
            if i == 0:
                g.edge(str(root.id), str(root.children[i].id), label='lower')
            elif i == 1:
                g.edge(str(root.id), str(root.children[i].id), label='upper')
            else:
                g.edge(str(root.id), str(root.children[i].id), label='step')


        elif isinstance(root, ComprehensionNode):
            if i == 0:
                g.edge(str(root.id), str(root.children[i].id), label='target')
            elif i == 1:
                g.edge(str(root.id), str(root.children[i].id), label='iter_obj')
            else:
                g.edge(str(root.id), str(root.children[i].id), label='ifs')


        elif isinstance(root, ListCompNode) or isinstance(root, SetCompNode) or isinstance(root, GeneratorExpNode):
            if i == 0:
                g.edge(str(root.id), str(root.children[i].id), label='elem')
            else:
                g.edge(str(root.id), str(root.children[i].id), label='gen_' + str(i - 1))

        elif isinstance(root, FunctionCall):
            if i == 0:
                g.edge(str(root.id), str(root.children[i].id), label='f_name')
            else:
                g.edge(str(root.id), str(root.children[i].id), label='arg_' + str(i-1))

        elif isinstance(root, LambdaNode):
            if i == len(root.children) - 1:
                g.edge(str(root.id), str(root.children[i].id), label='body')
            else:
                g.edge(str(root.id), str(root.children[i].id), label='arg_' + str(i))



        else:
            g.edge(str(root.id), str(root.children[i].id))

        fill_graph_helper(root.children[i], g, visited)


def render(root, output_name):

    g = graphviz.Digraph(format='png', strict=False)
    fill_graph_helper(root, g, [])
    g.render(output_name, view=True, cleanup=True)


def compute_peg(filename):

    apeg, function_def = compute_apeg(filename)

    peg = PEGBuilder(apeg, function_def)

    g = graphviz.Digraph(format='png', strict=False)
    root = peg.root
    fill_graph_helper(root, g, [])
    g.render(view=True, cleanup=True)

    return peg

