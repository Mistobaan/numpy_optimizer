from abstract_peg import Eval_APEGNode, Pass_APEGNode, THETA_APEGNode, Condition_APEGNode, True_APEGNode, False_APEGNode
from abstract_peg import APEGNode, PHI_APEGNode
from abstract_peg import compute_apeg
import ast
import astor


class PEGNode(object):

    def __init__(self):
        pass


class LiteralNode(PEGNode):

    def __init__(self, token):
        self.token = token


class Param(PEGNode):

    def __init__(self, _id, name):
        self.id = _id
        self.name = name
        self.children = []
        self.predecessors = []

    def __str__(self):
        return 'param_' + self.name


class BinOpNode(PEGNode):

    def __init__(self, _id, op, args):
        self.id = _id
        self.op = op
        self.children = args
        self.predecessors = []

    def __str__(self):
        return astor.dump_tree(self.op)


class BoolOpNode(PEGNode):

    def __init__(self, _id, op, args):
        self.id = _id
        self.op = op
        self.children = args
        self.predecessors = []

    def __str__(self):
        return astor.dump_tree(self.op)


class CompareNode(PEGNode):

    def __init__(self, _id, head, ops, tail):
        self.id = _id
        self.ops = ops
        self.children = [head] + tail
        self.predecessors = []

    def head(self):
        return self.children[0]

    def tail(self):
        return self.children[1:]

    def __str__(self):
        return astor.dump_tree(self.ops[0])





class PHINode(PEGNode):

    def __init__(self, _id, cond, t, f):
        self.id = _id
        self.cond = cond
        self.t = t
        self.f = f
        self.children = [self.cond, self.t, self.f]
        self.predecessors = []

    def __str__(self):
        return 'PHI'


class VariableNode(PEGNode):

    def __init__(self, _id, name):
        self.id = _id
        self.children = []
        self.name = name
        self.predecessors = []


    def __str__(self):
        return self.name + '_var'


class NumericNode(LiteralNode):

    def __init__(self, _id, token):
        self.id = _id
        self.children = []
        self.predecessors = []
        super().__init__(token)

    def value(self):
        return self.token.n

    def __str__(self):
        return str(self.value())


class StringNode(LiteralNode):

    def __init__(self, _id, token):
        self.id = _id
        self.children = []
        self.predecessors = []
        super().__init__(token)

    def value(self):
        return self.token.s

    def __str__(self):
        return self.value()


class NameConstantNode(LiteralNode):

    def __init__(self, _id, token):
        self.id = _id
        self.children = []
        self.predecessors = []
        super().__init__(token)

    def value(self):
        return self.token.value

    def __str__(self):
        return str(self.value())


class BytesNode(LiteralNode):

    def __init__(self, _id, token):
        self.id = _id
        self.children = []
        self.predecessors = []
        super().__init__(token)

    def value(self):
        return self.token.s

    def __str__(self):
        return str(self.value())


class ListNode(LiteralNode):

    def __init__(self, _id, children, token):
        self.id = _id
        self.children = children
        self.predecessors = []
        super().__init__(token)

    def elements(self):
        return self.token.elts

    def __str__(self):
        return 'List'


class SetNode(LiteralNode):

    def __init__(self, _id, children, token):
        self.id = _id
        self.children = children
        self.predecessors = []
        super().__init__(token)

    def elements(self):
        return self.token.elts

    def __str__(self):
        return 'Set'


class TupleNode(LiteralNode):

    def __init__(self, _id, children, token):
        self.id = _id
        self.children = children
        self.predecessors = []
        super().__init__(token)

    def elements(self):
        return self.token.elts

    def __str__(self):
        return 'Tuple'


class DictNode(LiteralNode):

    def __init__(self, _id, keys_list_node, values_list_node, token):
        self.id = _id
        self.children = [keys_list_node, values_list_node]
        self.predecessors = []
        super().__init__(token)

    def dictionary(self):
        return dict(zip(self.token.keys, self.token.values))

    def __str__(self):
        return 'Dict'


class AttributeNode(PEGNode):

    def __init__(self, _id, value, attr):
        self.id = _id
        self.predecessors = []
        self.attr = attr
        self.children = [value]


    def value(self):
        return self.children[0]


    def __str__(self):
        return self.attr + '_attr'


class SubscriptNode(PEGNode):

    def __init__(self, _id, value, slice):
        self.id = _id
        self.children = [value, slice]
        self.predecessors = []


    def value(self):
        return self.children[0]

    def slice(self):
        return self.children[1]

    def __str__(self):
        return 'Subscript'


class SliceNode(PEGNode):

    def __init__(self, _id, lower, upper, step):
        self.id = _id
        self.children = [lower, upper, step]
        self.predecessors = []



    def __str__(self):
        return 'Slice'


class IndexNode(PEGNode):

    def __init__(self, _id, value):
        self.id = _id
        self.children = [value]
        self.predecessors = []


    def __str__(self):
        return 'Index'


class ExtSliceNode(PEGNode):

    def __init__(self, _id, dims):
        self.id = _id
        self.children = dims
        self.predecessors = []


    def __str__(self):
        return 'ExtSlice'



class ComprehensionNode(PEGNode):

    def __init__(self, _id, target, iter, ifs):
        self.id = _id
        self.children = [target, iter, ifs]
        self.predecessors = []


    def __str__(self):
        return 'Comprehension'


class ListCompNode(PEGNode):

    def __init__(self, _id, element, generators):
        self.id = _id
        self.children = [element] + generators
        self.predecessors = []

    def element(self):
        return self.children[0]

    def generators(self):
        return self.children[1:]

    def __str__(self):
        return 'List Compr'


class SetCompNode(PEGNode):

    def __init__(self, _id, element, generators):
        self.id = _id
        self.children = [element] + generators
        self.predecessors = []

    def element(self):
        return self.children[0]

    def generators(self):
        return self.children[1:]

    def __str__(self):
        return 'Set Compr'

class GeneratorExpNode(PEGNode):

    def __init__(self, _id, element, generators):
        self.id = _id
        self.children = [element] + generators
        self.predecessors = []

    def element(self):
        return self.children[0]

    def generators(self):
        return self.children[1:]

    def __str__(self):
        return 'Generator Exp'


class DictCompNode(PEGNode):

    def __init__(self, _id, key, value, generators):
        self.id = _id
        self.children = [key, value] + generators
        self.predecessors = []

    def key(self):
        return self.children[0]

    def value(self):
        return self.children[1]

    def generators(self):
        return self.children[2:]

    def __str__(self):
        return 'Dict Compr'



class THETANode(PEGNode):

    def __init__(self, _id, base, step, loop_depth, var_name):
        self.id = _id
        self.base = base
        self.step = step
        self.children = [self.base, self.step]
        self.loop_depth = loop_depth
        self.predecessors = []
        self.var_name = var_name

    def __str__(self):
        return 'THETA_' + str(self.loop_depth) + ' (' + self.var_name + ')'


class EvalNode(PEGNode):

    def __init__(self, _id, loop_variant_node, idx_node):
        self.id = _id
        self.loop_variant_node = loop_variant_node
        self.idx_node = idx_node
        self.children = [self.loop_variant_node, self.idx_node]
        self.predecessors = []

    def __str__(self):
        return 'EVAL'


class PassNode(PEGNode):

    def __init__(self, _id, condition_node):
        self.id = _id
        self.condition_node = condition_node
        self.children = [self.condition_node]
        self.predecessors = []

    def __str__(self):
        return 'PASS'


class UnaryOpNode(PEGNode):

    def __init__(self, _id, op, operand):
        self.id = _id
        self.op = op
        self.children = [operand]
        self.predecessors = []

    def operand(self):
        return self.children[0]

    def __str__(self):
        return astor.dump_tree(self.op)


class TemporaryNode(PEGNode):

    def __init__(self, _id, name):
        self.id = _id
        self.name = name
        self.children = []
        self.predecessors = []

    def __str__(self):
        return 'tmp_' + self.name


class FunctionCall(PEGNode):

    def __init__(self, _id, name, args):
        self.id = _id
        self.name = name
        self.children = args
        self.predecessors = []

    def __str__(self):
        return self.name + '_func'


class PEG(object):

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
        self.remove_selfloops(self.eval_nodes)

        if isinstance(self.ctx['retvar'], EvalNode):

            theta_node = self.ctx['retvar'].children[0]
            if not isinstance(theta_node, THETANode):
                return self.ctx['retvar'].children[0]

            if theta_node.children[1] == theta_node:
                return theta_node.children[0]

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

        next_expr = ast.Call(func=ast.Name(id='next', ctx=ast.Load()), args=[loop_var], keywords=[])
        next_stmt = ast.Assign(targets=[loop_var], value=next_expr)

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
                                 PassNode(self.compute_id(), self.TE(break_condition, loop_header_ctx)))

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
                expr = stmt.value
                new_ctx[var.id] = self.TE(expr, new_ctx)

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

    def TE(self, expr, ctx):

        new_ctx = dict.copy(ctx)

        if isinstance(expr, ast.Name):

            if isinstance(new_ctx[expr.id], TemporaryNode):
                tmp_node = new_ctx[expr.id]
                return TemporaryNode(self.compute_id(), tmp_node.name)

            node = new_ctx[expr.id]
            return node

        if isinstance(expr, ast.Num):
            node = NumericNode(self.compute_id(), expr)

            return node

        if isinstance(expr, ast.Str):
            node = StringNode(self.compute_id(), expr)

            return node

        if isinstance(expr, ast.NameConstant):
            node = NameConstantNode(self.compute_id(), expr)

            return node

        if isinstance(expr, ast.List):
            elements = list(map(lambda e: self.TE(e, new_ctx), expr.elts))
            node = ListNode(self.compute_id(), elements, expr)

            return node

        if isinstance(expr, ast.Set):
            elements = list(map(lambda e: self.TE(e, new_ctx), expr.elts))
            node = SetNode(self.compute_id(), elements, expr)

            return node

        if isinstance(expr, ast.Tuple):
            elements = list(map(lambda e: self.TE(e, new_ctx), expr.elts))
            node = TupleNode(self.compute_id(), elements, expr)

            return node

        if isinstance(expr, ast.Dict):
            keys = list(map(lambda k: self.TE(k, new_ctx), expr.keys))
            values = list(map(lambda v: self.TE(v, new_ctx), expr.values))

            keys_node = ListNode(self.compute_id(), keys, ast.List(expr.keys, ast.Load()))
            values_node = ListNode(self.compute_id(), values, ast.List(expr.values, ast.Load()))
            node = DictNode(self.compute_id(), keys_node, values_node, expr)

            return node

        if isinstance(expr, ast.BinOp):
            op = expr.op
            args = [self.TE(expr.left, new_ctx), self.TE(expr.right, new_ctx)]
            node = BinOpNode(self.compute_id(), op, args)

            return node

        if isinstance(expr, ast.BoolOp):
            op = expr.op
            args = [self.TE(operand, new_ctx) for operand in expr.values]
            node = BoolOpNode(self.compute_id(), op, args)

            return node

        if isinstance(expr, ast.Compare):
            head = self.TE(expr.left, new_ctx)
            ops = expr.ops
            tail = [self.TE(operand, new_ctx) for operand in expr.comparators]
            node = CompareNode(self.compute_id(), head, ops, tail)

            return node

        if isinstance(expr, ast.UnaryOp):
            node = UnaryOpNode(self.compute_id(), expr.op, self.TE(expr.operand, new_ctx))
            return node

        if isinstance(expr, ast.Call):
            args = list(map(lambda a: self.TE(a, new_ctx), expr.args))

            name = expr.func.id

            node = FunctionCall(self.compute_id(), name, args)

            return node

        if isinstance(expr, ast.Attribute):

            value = self.TE(expr.value, new_ctx)

            node = AttributeNode(self.compute_id(), value, expr.attr)

            return node

        if isinstance(expr, ast.Subscript):

            value = self.TE(expr.value, new_ctx)
            slice = self.TE(expr.slice, new_ctx)

            node = SubscriptNode(self.compute_id(), value, slice)

            return node

        if isinstance(expr, ast.Index):

            value = self.TE(expr.value, new_ctx)

            node = IndexNode(self.compute_id(), value)

            return node


        if isinstance(expr, ast.Slice):

            none_expr = ast.NameConstant(None)

            lower = self.TE(expr.lower, new_ctx) if expr.lower != None else \
                NameConstantNode(self.compute_id(), none_expr)

            upper = self.TE(expr.upper, new_ctx) if expr.upper != None else \
                NameConstantNode(self.compute_id(), none_expr)

            step = self.TE(expr.step, new_ctx) if expr.step != None else \
                NameConstantNode(self.compute_id(), none_expr)

            node = SliceNode(self.compute_id(), lower, upper, step)

            return node


        if isinstance(expr, ast.ExtSlice):

            dims = [self.TE(dim, new_ctx) for dim in expr.dims]

            node = ExtSliceNode(self.compute_id(), dims)

            return node


        if isinstance(expr, ast.comprehension):

            if isinstance(expr.target, ast.Name):
                target = VariableNode(self.compute_id(), expr.target.id)
                ctx[target.name] = target

            else:
                target_vars = [VariableNode(self.compute_id(), arg.id) for arg in expr.target]
                for var in target_vars:
                    ctx[var.name] = var

                target = TupleNode(self.compute_id(), target_vars, expr.target)



            iter = self.TE(expr.iter, ctx)
            ifs = [self.TE(test, ctx) for test in expr.ifs]
            ifs_list = ListNode(self.compute_id(), ifs, expr.ifs)

            node = ComprehensionNode(self.compute_id(), target, iter, ifs_list)

            return node


        if isinstance(expr, ast.ListComp):

            generators = [self.TE(gen, ctx) for gen in expr.generators]
            elt = self.TE(expr.elt, ctx)


            node = ListCompNode(self.compute_id(), elt, generators)

            return node

        if isinstance(expr, ast.SetComp):

            generators = [self.TE(gen, ctx) for gen in expr.generators]
            elt = self.TE(expr.elt, ctx)

            node = SetCompNode(self.compute_id(), elt, generators)

            return node

        if isinstance(expr, ast.GeneratorExp):

            generators = [self.TE(gen, ctx) for gen in expr.generators]
            elt = self.TE(expr.elt, ctx)

            node = GeneratorExpNode(self.compute_id(), elt, generators)

            return node

        if isinstance(expr, ast.DictComp):

            generators = [self.TE(gen, ctx) for gen in expr.generators]
            key = self.TE(expr.key, ctx)
            value = self.TE(expr.value, ctx)

            node = ListCompNode(self.compute_id(), key, value, generators)

            return node


        print('UNRECOGNIZED TYPE expr:', type(expr))

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

    def EVAL(self, ctx, node):

        new_ctx = dict.copy(ctx)

        return self.init_map(new_ctx.keys(),
                             lambda k: EvalNode(self.compute_id(), new_ctx[k], node))

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

    def _fixpoint_temps_helper(self, ctx, node, visited, nodes_to_change):

        if node in visited:
            return

        visited.append(node)

        if isinstance(node, TemporaryNode):
            nodes_to_change.append(node)

        for child in node.children:
            self._fixpoint_temps_helper(ctx, node, visited, nodes_to_change)

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

        i = 0
        while i < len(eval_nodes):

            if not isinstance(eval_nodes[i].children[0], THETANode):
                i = i + 1
                continue

            theta_node = eval_nodes[i].children[0]
            theta_init = theta_node.children[0]

            if theta_node == theta_node.children[1]:

                for pred in theta_node.predecessors:
                    idx = pred.children.index(theta_node)
                    pred.children[idx] = theta_node.children[0]
                    theta_init.predecessors.append(pred)

                theta_init.predecessors.remove(theta_node)

                for eval_predecessor in eval_nodes[i].predecessors:

                    idx = eval_predecessor.children.index(eval_nodes[i])
                    eval_predecessor.children[idx] = theta_init

                    theta_init.predecessors.append(eval_predecessor)

                    if isinstance(theta_init, EvalNode):

                        eval_node = theta_init

                        if eval_node.children[0] == eval_node.children[0].children[1]:
                            eval_nodes.append(theta_init)

                    if isinstance(theta_init, THETANode):

                        if theta_init == theta_init.children[1]:
                            eval_node = list(filter(lambda e: isinstance(e, EvalNode),
                                                    theta_init.predecessors))[0]

                            eval_nodes.append(eval_node)

            i = i + 1


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
            if i == 0:
                g.edge(str(root.id), str(root.children[i].id), label='keys')
            else:
                g.edge(str(root.id), str(root.children[i].id), label='values')


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

        else:
            g.edge(str(root.id), str(root.children[i].id))

        fill_graph_helper(root.children[i], g, visited)


def compute_peg(filename):
    apeg, function_def = compute_apeg(filename)

    g = graphviz.Digraph(format='png', strict=False)
    root = apeg.apeg_root
    fill_graph_helper(root, g, [])
    # g.render(view=True, cleanup=True)

    peg = PEG(apeg, function_def)

    g = graphviz.Digraph(format='png', strict=False)
    root = peg.root
    fill_graph_helper(root, g, [])
    g.render(view=True, cleanup=True)

    return peg

