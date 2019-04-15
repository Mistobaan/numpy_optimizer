import ast
import astor

class PEGNode(object):

    def __init__(self):
        self.predecessors = []


class LeafNode(PEGNode):

    def __init__(self, token):
        super().__init__()
        self.children = []
        self.token = token


class Param(LeafNode):

    def __init__(self, _id, name):
        self.id = _id
        self.name = name
        token = ast.Name(id=self.name, ctx=ast.Load())
        super().__init__(token)

    def __str__(self):
        return 'param_' + self.name


class BinOpNode(PEGNode):

    def __init__(self, _id, op, args):
        super().__init__()
        self.id = _id
        self.op = op
        self.children = args

    def __str__(self):
        return astor.dump_tree(self.op)


class BoolOpNode(PEGNode):

    def __init__(self, _id, op, args):
        super().__init__()
        self.id = _id
        self.op = op
        self.children = args

    def __str__(self):
        return astor.dump_tree(self.op)


class CompareNode(PEGNode):

    def __init__(self, _id, head, ops, tail):
        super().__init__()
        self.id = _id
        self.ops = ops
        self.children = [head] + tail

    def head(self):
        return self.children[0]

    def tail(self):
        return self.children[1:]

    def __str__(self):
        return astor.dump_tree(self.ops[0])





class PHINode(PEGNode):

    def __init__(self, _id, cond, t, f):
        super().__init__()
        self.id = _id
        self.cond = cond
        self.t = t
        self.f = f
        self.children = [self.cond, self.t, self.f]

    def __str__(self):
        return 'PHI'


class VariableNode(LeafNode):

    def __init__(self, _id, name):
        self.id = _id
        self.name = name
        token = ast.Name(id=self.name, ctx=ast.Load())
        super().__init__(token)


    def __str__(self):
        return self.name


class NumericNode(LeafNode):

    def __init__(self, _id, token):
        self.id = _id
        super().__init__(token)

    def value(self):
        return self.token.n

    def __str__(self):
        return str(self.value())


class StringNode(LeafNode):

    def __init__(self, _id, token):
        self.id = _id
        super().__init__(token)

    def value(self):
        return self.token.s

    def __str__(self):
        return  '\'' + self.value() + '\''


class NameConstantNode(LeafNode):

    def __init__(self, _id, token):
        self.id = _id
        super().__init__(token)

    def value(self):
        return self.token.value

    def __str__(self):
        return str(self.value())


class BytesNode(LeafNode):

    def __init__(self, _id, token):
        self.id = _id
        super().__init__(token)

    def value(self):
        return self.token.s

    def __str__(self):
        return str(self.value())


class ListNode(PEGNode):

    def __init__(self, _id, children):
        self.id = _id
        self.children = children
        super().__init__()


    def __str__(self):
        return 'List'


class SetNode(PEGNode):

    def __init__(self, _id, children):
        self.id = _id
        self.children = children
        super().__init__()


    def __str__(self):
        return 'Set'


class TupleNode(PEGNode):

    def __init__(self, _id, children):
        self.id = _id
        self.children = children
        super().__init__()


    def __str__(self):
        return 'Tuple'


class DictNode(PEGNode):

    def __init__(self, _id, keys, values):
        self.id = _id
        self.children = keys + values
        super().__init__()


    def n(self):
        return len(self.children)

    def keys(self):
        return self.children[0 : int(self.n() / 2)]

    def values(self):
        return self.children[int(self.n() / 2) :]

    def __str__(self):
        return 'Dict'


class AttributeNode(PEGNode):

    def __init__(self, _id, value, attr):
        self.id = _id
        self.attr = attr
        self.children = [value]
        super().__init__()


    def value(self):
        return self.children[0]


    def __str__(self):
        return self.attr + '_attr'


class SubscriptNode(PEGNode):

    def __init__(self, _id, value, slice):
        self.id = _id
        self.children = [value, slice]
        super().__init__()


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
        super().__init__()

    def lower(self):
        return self.children[0]

    def upper(self):
        return self.children[1]

    def step(self):
        return self.children[2]


    def __str__(self):
        return 'Slice'


class IndexNode(PEGNode):

    def __init__(self, _id, value):
        self.id = _id
        self.children = [value]
        super().__init__()


    def value(self):
        return self.children[0]


    def __str__(self):
        return 'Index'


class ExtSliceNode(PEGNode):

    def __init__(self, _id, dims):
        self.id = _id
        self.children = dims
        super().__init__()

    def dims(self):
        return self.children


    def __str__(self):
        return 'ExtSlice'



class ComprehensionNode(PEGNode):

    def __init__(self, _id, target, iter, ifs):
        self.id = _id
        self.children = [target, iter] + ifs
        super().__init__()


    def target(self):
        return self.children[0]

    def iter_obj(self):
        return self.children[1]

    def ifs(self):
        return self.children[2:]


    def __str__(self):
        return 'Comprehension'


class ListCompNode(PEGNode):

    def __init__(self, _id, element, generators):
        self.id = _id
        self.children = [element] + generators
        super().__init__()

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
        super().__init__()

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
        super().__init__()

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
        super().__init__()

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
        self.var_name = var_name
        super().__init__()

    def __str__(self):
        return 'THETA_' + str(self.loop_depth) + ' (' + self.var_name + ')'


class EvalNode(PEGNode):

    def __init__(self, _id, loop_variant_node, idx_node, loop_depth):
        self.id = _id
        self.loop_variant_node = loop_variant_node
        self.idx_node = idx_node
        self.children = [self.loop_variant_node, self.idx_node]
        self.loop_depth = loop_depth
        super().__init__()

    def __str__(self):
        return 'EVAL_' + str(self.loop_depth)


class PassNode(PEGNode):

    def __init__(self, _id, condition_node):
        self.id = _id
        self.condition_node = condition_node
        self.children = [self.condition_node]
        super().__init__()

    def __str__(self):
        return 'PASS'


class UnaryOpNode(PEGNode):

    def __init__(self, _id, op, operand):
        self.id = _id
        self.op = op
        self.children = [operand]
        super().__init__()

    def operand(self):
        return self.children[0]

    def __str__(self):
        return astor.dump_tree(self.op)


class TemporaryNode(PEGNode):

    def __init__(self, _id, name):
        self.id = _id
        self.name = name
        self.children = []
        super().__init__()

    def __str__(self):
        return 'tmp_' + self.name


class FunctionCall(PEGNode):

    def __init__(self, _id, name, args):
        self.id = _id
        self.children = [name] + args
        super().__init__()


    def name(self):
        return self.children[0]

    def args(self):
        return self.children[1:]

    def __str__(self):
        return 'Function Call'


class LambdaNode(PEGNode):

    def __init__(self, _id, args, body):
        super().__init__()
        self.id = _id
        self.children = args + [body]

    def args(self):
        return self.children[:-1]

    def body(self):
        return self.children[-1]

    def __str__(self):
        return 'Lambda'

