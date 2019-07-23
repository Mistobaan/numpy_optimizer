import ast
import astor

class PEGNode(object):

    def __init__(self, _id):
        self.id = _id
        self.predecessors = []
        self.children = []
        self.eq_class = 'class' + str(_id)
        self.expr_type = 'unknown'
        self.cost = 1
        self.loop_variance_indices = set([])


    def compute_expr_type(self):
        return 'unknown'


    def evaluable(self):
        return False

    def __str__(self):
        return 'PEGNode'

    def type_name(self):
        return type(self).__name__ + '_'


    def same(self, other):
        return self == other

    def is_constant_class(self):
        return self.eq_class.find('class') < 0


class LeafNode(PEGNode):

    def __init__(self, _id, token=None):
        super().__init__(_id)
        self.token = token
        self.expr_type = type(self).__name__
        self.cost = 0

    def type_name(self):
        return super().type_name() + str(self)

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
            return False

        if len(self.children) != len(other.children):
            return False

        return all([ch == oth_ch for (ch, oth_ch) in zip(self.children, other.children)])


class Param(LeafNode):

    def __init__(self, _id, name=None):
        self.name = name
        token = ast.Name(id=self.name, ctx=ast.Load())
        super().__init__(_id, token)
        self.eq_class = 'param-' + self.name

    def __str__(self):
        return 'param_' + self.name


    def type_name(self):
        return type(self).__name__ + '_' + self.name


class BinOpNode(PEGNode):

    def __init__(self, _id, op=None, args=[]):
        super().__init__(_id)
        self.op = op
        self.children = args
        self.expr_type = self.compute_expr_type()
        self.cost = 1000 if any([isinstance(c, NPArrayNode) for c in self.children]) else 1

    def left(self):
        return self.children[0]

    def right(self):
        return self.children[1]

    def compute_expr_type(self):
        if len(self.children) == 0:
            return 'unknown'
        return 'NumNode' if all([arg.compute_expr_type() == 'NumNode' for arg in self.children]) else 'unknown'

    def __str__(self):
        return astor.dump_tree(self.op) if self.op != None else '?'

    def type_name(self):
        return super().type_name() + str(self)

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
            return False

        if len(self.children) != len(other.children):
            return False

        return all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])


class BoolOpNode(PEGNode):

    def __init__(self, _id, op=None, args=[]):
        super().__init__(_id)
        self.op = op
        self.children = args
        self.expr_type = 'NameConstantNode'

    def left(self):
        return self.children[0]

    def right(self):
        return self.children[1]

    def __str__(self):
        return astor.dump_tree(self.op) if self.op != None else '?'

    def type_name(self):
        return super().type_name() + str(self)

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
            return False

        if len(self.children) != len(other.children):
            return False

        return all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])


class CompareNode(PEGNode):

    def __init__(self, _id, ops, children=[]):
        super().__init__(_id)
        self.ops = ops
        self.children = children
        self.expr_type = 'NameConstantNode'

    def head(self):
        return self.children[0]

    def tail(self):
        return self.children[1:]

    def __str__(self):
        return '_'.join([astor.dump_tree(op) for op in self.ops])

    def type_name(self):
        return super().type_name() + str(self)

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
            return False

        if len(self.children) != len(other.children):
            return False

        return all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])


class PHINode(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children
        self.expr_type = self.compute_expr_type()
        self.cost = 10

    def compute_expr_type(self):
        if len(self.children) == 0:
            return 'unknown'

        if self.children[1].expr_type != self.children[2].expr_type:
            return 'unknown'

        return self.children[1].expr_type

    def cond(self):
        return self.children[0] if len(self.children) > 0 else None

    def t(self):
        return self.children[1] if len(self.children) > 0 else None

    def f(self):
        return self.children[2] if len(self.children) > 0 else None

    def __str__(self):
        return 'PHI'

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
            return False

        if len(self.children) != len(other.children):
            return False

        return all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])


class VariableNode(LeafNode):

    def __init__(self, _id, name=None):
        self.name = name
        token = ast.Name(id=self.name, ctx=ast.Load())
        super().__init__(_id, token)

    def __str__(self):
        return (self.name + '_var') if self.name != None else '?'

    def type_name(self):
        return type(self).__name__ + '_' + self.name


class IdentifierNode(LeafNode):

    def __init__(self, _id, name=None):
        self.name = name
        token = ast.Name(id=self.name, ctx=ast.Load())
        super().__init__(_id, token)

    def __str__(self):
        return self.name if self.name != None else '?'

    def type_name(self):
        return super().type_name()


class NumNode(LeafNode):

    def __init__(self, _id, token=None):
        super().__init__(_id, token)
        self.eq_class = 'num-' + str(self)

    def evaluable(self):
        return True

    def value(self):
        return self.token.n

    def __str__(self):
        return str(self.value()) if self.token != None else '?'


class StrNode(LeafNode):

    def __init__(self, _id, token=None):
        super().__init__(_id, token)
        self.eq_class = 'str' + str(self)

    def evaluable(self):
        return True

    def value(self):
        return self.token.s

    def __str__(self):
        return  '\'' + (self.value() if self.token != None else '?') + '\''


class NameConstantNode(LeafNode):

    def __init__(self, _id, token=None):
        super().__init__(_id, token)
        self.eq_class = 'val' + str(self)

    def evaluable(self):
        return True

    def value(self):
        return self.token.value

    def __str__(self):
        return str(self.value()) if self.token != None else '?'


class BytesNode(LeafNode):

    def __init__(self, _id, token=None):
        super().__init__(_id, token)
        self.eq_class = 'bytes-' + str(self)

    def value(self):
        return self.token.s

    def __str__(self):
        return str(self.value()) if self.token != None else '?'


class ListNode(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children
        self.expr_type = self.compute_expr_type()

    def compute_expr_type(self):

        return 'ListNode'

    def __str__(self):
        return 'List'

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
            return False

        if len(self.children) != len(other.children):
            return False

        return all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])


class SetNode(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children
        self.expr_type = self.compute_expr_type()

    def compute_expr_type(self):
        if len(self.children) == 0:
            return 'unknown'

        return 'SetNode[' + self.children[0].expr_type + ']'


    def __str__(self):
        return 'Set'

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
            return False

        if len(self.children) != len(other.children):
            return False

        return all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])


class TupleNode(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children
        self.expr_type = 'unknown'

    def __str__(self):
        return 'Tuple'

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
            return False

        if len(self.children) != len(other.children):
            return False

        return all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])


class DictNode(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children
        self.expr_type = self.compute_expr_type()

    def compute_expr_type(self):

        if len(self.children) == 0:
            return 'unknown'

        return 'Dict[' + self.keys()[0].expr_type + ', ' + self.values()[0].expr_type() + ']'

    def n(self):
        return len(self.children)

    def keys(self):
        return self.children[0 : int(self.n() / 2)]

    def values(self):
        return self.children[int(self.n() / 2) :]

    def __str__(self):
        return 'Dict'

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
            return False

        if len(self.children) != len(other.children):
            return False

        return all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])


class AttributeNode(PEGNode):

    def __init__(self, _id, attr, value_child):
        super().__init__(_id)
        self.attr = attr
        self.children = value_child
        self.cost = 3

    def value(self):
        return self.children[0]

    def __str__(self):
        return (self.attr + '_attr') if self.attr != None else '?'

    def type_name(self):
        return super().type_name() + self.attr

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
            return False

        if len(self.children) != len(other.children):
            return False

        return all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])


class SubscriptNode(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children

    def value(self):
        return self.children[0]

    def slice(self):
        return self.children[1]

    def __str__(self):
        return 'Subscript'


class SliceNode(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children

    def lower(self):
        return self.children[0]

    def upper(self):
        return self.children[1]

    def step(self):
        return self.children[2]

    def __str__(self):
        return 'Slice'


class IndexNode(PEGNode):

    def __init__(self, _id, value_child):
        super().__init__(_id)
        self.children = value_child

    def value(self):
        return self.children[0]

    def __str__(self):
        return 'Index'


class ExtSliceNode(PEGNode):

    def __init__(self, _id, dims):
        super().__init__(_id)
        self.children = dims

    def dims(self):
        return self.children

    def __str__(self):
        return 'ExtSlice'


class ComprehensionNode(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children

    def target(self):
        return self.children[0]

    def iter_obj(self):
        return self.children[1]

    def ifs(self):
        return self.children[2:]

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
                return False

        if len(self.children) != len(other.children):
                return False

        res = all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])

        return res


    def __str__(self):
        return 'Comprehension'


class ListCompNode(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children

    def element(self):
        return self.children[0]

    def generators(self):
        return self.children[1:]

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
                return False

        if len(self.children) != len(other.children):
                return False

        res = all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])

        return res


    def __str__(self):
        return 'List Compr'


class SetCompNode(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children

    def element(self):
        return self.children[0]

    def generators(self):
        return self.children[1:]

    def __str__(self):
        return 'Set Compr'


class GeneratorExpNode(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children

    def element(self):
        return self.children[0]

    def generators(self):
        return self.children[1:]

    def __str__(self):
        return 'Generator Exp'


class DictCompNode(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children

    def key(self):
        return self.children[0]

    def value(self):
        return self.children[1]

    def generators(self):
        return self.children[2:]

    def __str__(self):
        return 'Dict Compr'


class THETANode(PEGNode):

    def __init__(self, _id, children=[], loop_depth=None, var_name=None):
        super().__init__(_id)
        self.children = children
        self.loop_depth = loop_depth if loop_depth != None else ('?loop-d-' + str(_id))
        self.var_name = var_name if var_name != None else ('$?arg_' + str(_id))
        self.expr_type = self.compute_expr_type()
        self.cost = 10

    def compute_expr_type(self):
        if len(self.children) == 0:
            return 'unknown'
        return 'NumNode' if all([arg.expr_type == 'NumNode' for arg in self.children]) else 'unknown'

    def type_name(self):
        return type(self).__name__ + '_' + self.var_name

    def __str__(self):
        if self.loop_depth == None or self.var_name == None:
            return 'THETA_?'
        return 'THETA_' + str(self.loop_depth) + ' (' + self.var_name + ')'


class EvalNode(PEGNode):

    def __init__(self, _id, children=[], loop_depth=None):
        super().__init__(_id)
        self.children = children
        self.loop_depth = loop_depth
        self.expr_type = children[0].expr_type if len(children) > 0 else 'unknown'
        self.cost = 10

    def __str__(self):
        return 'EVAL_' + str(self.loop_depth)


class PassNode(PEGNode):

    def __init__(self, _id, children=[], loop_depth=None):
        super().__init__(_id)
        self.children = children
        self.expr_type = 'unknown'
        self.loop_depth = loop_depth

    def __str__(self):
        return 'PASS'

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
            return False

        if len(self.children) != len(other.children):
            return False

        return all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])


class UnaryOpNode(PEGNode):

    def __init__(self, _id, op, children=[]):
        super().__init__(_id)
        self.op = op
        self.children = children
        self.expr_type = self.operand().expr_type if self.children != [] else 'unknown'

    def operand(self):
        return self.children[0]

    def __str__(self):
        return astor.dump_tree(self.op)

    def type_name(self):
        return super().type_name() + str(self)

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
            return False

        if len(self.children) != len(other.children):
            return False

        return all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])


class TemporaryNode(PEGNode):

    def __init__(self, _id, name):
        super().__init__(_id)
        self.name = name
        self.children = []

    def __str__(self):
        return 'tmp_' + self.name


class FunctionCall(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children
        self.cost = 15

    def name(self):
        return self.children[0]

    def args(self):
        return self.children[1:]

    def __str__(self):
        return 'Function Call'

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
            return False

        if len(self.children) != len(other.children):
            return False

        return all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])


class IfExpNode(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children

    def cond(self):
        return self.children[0]

    def t(self):
        return self.children[1]

    def f(self):
        return self.children[2]

    def __str__(self):
        return 'IfExp'

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
            return False

        if len(self.children) != len(other.children):
            return False

        return all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])



class LambdaNode(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children
        self.expr_type = self.body().expr_type

    def args(self):
        return self.children[:-1]

    def body(self):
        return self.children[-1]

    def __str__(self):
        return 'Lambda'

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
            return False

        if len(self.children) != len(other.children):
            return False

        return all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])


class NPArrayNode(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children
        self.expr_type = 'NPArrayNode'
        self.shape = compute_shape(self) if len(children) > 0 else None

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
            return False

        if len(self.children) != len(other.children):
            return False

        res = all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])

        return res

    def __str__(self):
        return 'NPArray'


class SetSubscriptNode(PEGNode):

    def __init__(self, _id, children=[]):
        super().__init__(_id)
        self.children = children
        self.expr_type = 'unknown'

    def same(self, other):

        if self.type_name() != other.type_name():
            return False

        if str(self) != str(other):
                return False

        if len(self.children) != len(other.children):
                return False

        res = all([ch.same(oth_ch) for (ch, oth_ch) in zip(self.children, other.children)])

        return res

    def target(self):
        return self.children[0]

    def slice(self):
        return self.children[1]

    def value(self):
        return self.children[2]

    def __str__(self):
        return 'SetSubscrip'


# computes shape of given arr node, if shape is unknown returns None
def compute_shape(arr_node):

    assert(isinstance(arr_node, NPArrayNode))

    shape = []
    visited = []

    compute_shape_helper(arr_node.children[0], [], shape, visited)


    return tuple(shape) if shape != [] else None


def compute_shape_helper(node, current_shape, shape, visited):

    if node.id in visited or shape != []:
        return

    visited.append(node.id)

    current_shape = current_shape + [len(node.children)]

    for child in node.children:
        compute_shape_helper(child, current_shape, shape, visited)


    if isinstance(node, ListNode) and any([child.expr_type == 'NumNode' for child in node.children]):

        for dim in current_shape:
            shape.append(dim)

