from peg_nodes import LeafNode, BinOpNode, THETANode, BoolOpNode, CompareNode, PHINode, NameConstantNode
import ast
import peg_nodes


def is_foldable(node):

    if isinstance(node, THETANode):
        return False

    if isinstance(node, PHINode):
        return node.cond().evaluable()

    return len(node.children) > 0 and all([child.evaluable() for child in node.children])


def filter_constant_classes(epeg):

    # filtering eq_class
    for class_id, nodes in epeg.classes.items():
        if class_id.find('class') < 0:

            nodes_to_remove = [n for n in nodes if not isinstance(n, LeafNode)]
            leaf_node = [n for n in nodes if isinstance(n, LeafNode)][0]

            for n in nodes_to_remove:
                epeg.replace_node(n, leaf_node)



from peg_nodes import EvalNode, NumNode

def remove_useless_evals(epeg):

    nodes_to_remove = []

    for node in epeg.nodes.values():

        if isinstance(node, EvalNode) and isinstance(node.children[1], NumNode) and node.children[1].value() == 0:
            epeg.classes[node.eq_class].remove(node)
            if node.children[0].children[0] not in epeg.classes[node.eq_class]:
                epeg.classes[node.eq_class].append(node.children[0].children[0])

            nodes_to_remove.append(node)


    for node_id, node in epeg.nodes.items():
        for i in range(len(node.children)):
            child_eq_class = node.children[i].eq_class

            if child_eq_class in [ntr.eq_class for ntr in nodes_to_remove]:
                node.children[i] = epeg.classes[child_eq_class][0]

    for node in nodes_to_remove:
        del epeg.nodes[node.id]


def constant_fold(node):

    if isinstance(node, BinOpNode):

        return constant_fold_binop(node)

    elif isinstance(node, BoolOpNode):

        return constant_fold_boolop(node)

    elif isinstance(node, CompareNode):

        return constant_fold_compare(node)

    elif isinstance(node, PHINode):

        return constant_fold_phi(node)

    return None


def constant_fold_phi(node):

    assert(node.cond().evaluable())

    if isinstance(node.cond(), NameConstantNode):

        if node.cond().value() == True:
            return node.t()

        # False and None case
        else:
            return node.f()

    return None



def constant_fold_binop(node):

    left = node.left()
    right = node.right()
    op = node.op

    expr = None

    if left.evaluable() and right.evaluable():

        left_val = left.value()
        right_val = right.value()

        if isinstance(op, ast.Add):
            expr = left_val + right_val

        elif isinstance(op, ast.Mult):
            expr = left_val * right_val

        elif isinstance(op, ast.Sub):
            expr = left_val - right_val

        elif isinstance(op, ast.Div):
            expr = left_val / right_val

        elif isinstance(op, ast.FloorDiv):
            expr = left_val // right_val

        elif isinstance(op, ast.Mod):
            expr = left_val % right_val

        elif isinstance(op, ast.Pow):
            expr = left_val ** right_val

        elif isinstance(op, ast.LShift):
            expr = left_val << right_val

        elif isinstance(op, ast.RShift):
            expr = left_val >> right_val

        elif isinstance(op, ast.BitOr):
            expr = left_val | right_val

        elif isinstance(op, ast.BitAnd):
            expr = left_val & right_val

        elif isinstance(op, ast.BitXor):
            expr = left_val ^ right_val

        elif isinstance(op, ast.MatMult):
            expr = left_val @ right_val

        if expr != None:

            expr = ast.parse(str(expr)).body[0].value
            type_name = type(expr).__name__
            new_node = getattr(peg_nodes, type_name + 'Node')(node.id, expr)

            return new_node


    return None


def constant_fold_boolop(node):

    left = node.left()
    right = node.right()
    op = node.op

    expr = None

    if left.evaluable() and right.evaluable():
        left_val = left.value()
        right_val = right.value()

        if isinstance(op, ast.And):
            expr = left_val and right_val

        elif isinstance(op, ast.Or):
            expr = left_val or right_val

    if expr != None:

        expr = ast.parse(str(expr)).body[0].value
        type_name = type(expr).__name__
        new_node = getattr(peg_nodes, type_name + 'Node')(node.id, expr)

        return new_node

    return None


def constant_fold_compare(node):

    left = node.head()
    ops = node.ops
    tail = node.tail()

    expr = None

    if left.evaluable() and all([arg.evaluable() for arg in tail]):

        left_val = left.value()
        tail_vals = [arg.value() for arg in tail]

        current_val = left_val
        expr = True

        for op, arg in zip(ops, tail_vals):

            if isinstance(op, ast.Eq):
                expr = expr and (current_val == arg)

            elif isinstance(op, ast.NotEq):
                expr = expr and (current_val != arg)

            elif isinstance(op, ast.Lt):
                expr = expr and (current_val < arg)

            elif isinstance(op, ast.LtE):
                expr = expr and (current_val <= arg)

            elif isinstance(op, ast.Gt):
                expr = expr and (current_val > arg)

            elif isinstance(op, ast.GtE):
                expr = expr and (current_val >= arg)

            elif isinstance(op, ast.Is):
                expr = expr and (current_val is arg)

            elif isinstance(op, ast.IsNot):
                expr = expr and (current_val is not arg)

            elif isinstance(op, ast.In):
                expr = expr and (current_val in arg)

            elif isinstance(op, ast.NotIn):
                expr = expr and (current_val not in arg)

            current_val = arg

    if expr != None:

        expr = ast.parse(str(expr)).body[0].value
        type_name = type(expr).__name__
        new_node = getattr(peg_nodes, type_name + 'Node')(node.id, expr)

        return new_node

    return None


def apply_constant_folding(epeg):

    foldable_nodes = [node for node in epeg.nodes.values() if is_foldable(node)]
    processed_nodes = [node.id for node in foldable_nodes]

    while foldable_nodes:

        node = foldable_nodes.pop()
        if node.id not in epeg.nodes.keys() or node.eq_class not in epeg.classes.keys():
            continue

        folded_node = constant_fold(node)

        if folded_node != None:

            folded_node = epeg.get_unique_node(folded_node)
            epeg.replace_node(node, folded_node)


            for node in epeg.nodes.values():
                if is_foldable(node):

                    foldable_nodes.insert(0, node)
                    processed_nodes.append(node.id)

        empty_classes = [eq_class for eq_class in epeg.classes.keys() if len(epeg.classes[eq_class]) == 0]

        for cl in empty_classes:
            del epeg.classes[cl]





