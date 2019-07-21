from peg_nodes import ListNode, NPArrayNode, BinOpNode
import numpy as np
from optimization_utils import constant_fold


def ndarray_node_to_array_of_ids_helper(node):

    if not isinstance(node, ListNode):
        return node.id

    children_list = [ndarray_node_to_array_of_ids_helper(child) for child in node.children]
    return children_list


def ndarray_node_to_array_of_ids(node):

    list_node = node.children[0]
    return np.array(ndarray_node_to_array_of_ids_helper(list_node))


def pair_ndarray_to_tree(arr, op, epeg):

    lists = pair_ndarray_to_tree_helper(arr, op, epeg)
    ndarray_node = NPArrayNode(epeg.compute_node_id(), [lists])

    epeg.nodes[ndarray_node.id] = ndarray_node
    epeg.add_node_to_eq_class(ndarray_node, ndarray_node.eq_class)
    lists.predecessors.append(ndarray_node)

    return ndarray_node


def pair_ndarray_to_tree_helper(arr, op, epeg):

    if len(arr.shape) == 0:
        # unpack pair ids
        fst_id, snd_id = arr
        n1 = epeg.nodes[fst_id]
        n2 = epeg.nodes[snd_id]
        binop_elt = BinOpNode(epeg.compute_node_id(), op=op, args=[n1, n2])
        binop_elt = epeg.get_unique_node(binop_elt)

        folded = constant_fold(binop_elt)
        if folded != None:
            binop_elt = folded

        n1.predecessors.append(binop_elt)
        n2.predecessors.append(binop_elt)
        epeg.nodes[binop_elt.id] = binop_elt
        epeg.add_node_to_eq_class(binop_elt, binop_elt.eq_class)
        return binop_elt

    children = [pair_ndarray_to_tree_helper(a, op, epeg) for a in arr]

    list_node = ListNode(epeg.compute_node_id(), children)
    epeg.nodes[list_node.id] = list_node
    epeg.add_node_to_eq_class(list_node, list_node.eq_class)
    for c in children:
        c.predecessors.append(list_node)

    return list_node


def broadcast(arr1, arr2, op, epeg):

    arr1_ids_array = ndarray_node_to_array_of_ids(arr1)
    arr2_ids_array = ndarray_node_to_array_of_ids(arr2)

    z = []

    for i, j in np.nditer([arr1_ids_array, arr2_ids_array]):
        z.append((i, j))

    z = np.array(z, dtype=[('fst', 'i4'), ('snd', 'i4')])
    shape = broadcasting_result_shape(arr1_ids_array.shape, arr2_ids_array.shape)
    result = pair_ndarray_to_tree(z.reshape(shape), op, epeg)

    return result


def broadcasting_result_shape(fst_shape, snd_shape):

    fst_shape = list(fst_shape)
    snd_shape = list(snd_shape)

    len_diff = len(fst_shape) - len(snd_shape)
    if len_diff > 0:
        snd_shape = ([1] * len_diff) + snd_shape
    elif len_diff < 0:
        fst_shape = ([1] * (-len_diff)) + fst_shape

    result_shape = [max(fst, snd) for (fst, snd) in zip(fst_shape, snd_shape)]
    return tuple(result_shape)


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


def is_broadcastable(arr_node):

    shape = compute_shape(arr_node)

    if shape is None:
        return False

    return is_broadcastable_helper(arr_node.children[0], shape, 0)


def is_broadcastable_helper(node, shape, dim_idx):

    if dim_idx >= len(shape):
        return True

    return len(node.children) == shape[dim_idx] and all([is_broadcastable_helper(child, shape, dim_idx + 1)]
                                                        for child in node.children)


def apply_broadcasting(epeg):

    epeg.current_node_id = max(epeg.nodes.keys()) + 1

    binops_of_broadcastables = [n for n in epeg.nodes.values() if isinstance(n, BinOpNode)
                           and all([isinstance(c, NPArrayNode) and is_broadcastable(c) for c in n.children])]


    while binops_of_broadcastables:

        binop = binops_of_broadcastables.pop()
        new_node = broadcast(binop.left(), binop.right(), binop.op, epeg)
        epeg.replace_node(binop, new_node)

        for pred in new_node.predecessors:
            if isinstance(pred, BinOpNode)  and \
                all([isinstance(c, NPArrayNode) and is_broadcastable(c) for c in pred.children]):
                binops_of_broadcastables.append(pred)

    empty_classes = [eq_class for eq_class in epeg.classes.keys() if len(epeg.classes[eq_class]) == 0]

    for cl in empty_classes:
        del epeg.classes[cl]