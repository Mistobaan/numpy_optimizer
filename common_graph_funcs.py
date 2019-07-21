import graphviz
import peg_nodes


def fill_graph_helper(root, g, visited):
    if root in visited:
        return

    visited.append(root)

    g.node(str(root.id), label=str(root))

    for i in range(len(root.children)):

        if isinstance(root, peg_nodes.PHINode):
            if i == 0:
                g.edge(str(root.id), str(root.children[i].id), label='cond')
            elif i == 1:
                g.edge(str(root.id), str(root.children[i].id), label='t')
            else:
                g.edge(str(root.id), str(root.children[i].id), label='f')

        elif isinstance(root, peg_nodes.THETANode):
            if i == 0:
                g.edge(str(root.id), str(root.children[i].id), label='init')
            elif i == 1:
                g.edge(str(root.id), str(root.children[i].id), label='iter')

        elif isinstance(root, peg_nodes.ListNode) or isinstance(root, peg_nodes.TupleNode) or \
                isinstance(root, peg_nodes.ExtSliceNode):
            g.edge(str(root.id), str(root.children[i].id), label=str(i))

        elif isinstance(root, peg_nodes.DictNode):
            if i in range(0, int(len(root.children) / 2)):
                g.edge(str(root.id), str(root.children[i].id), label='k_' + str(i))
            else:
                g.edge(str(root.id), str(root.children[i].id), label='v_' + str(i - int(len(root.children) / 2)))

        elif isinstance(root, peg_nodes.SliceNode):
            if i == 0:
                g.edge(str(root.id), str(root.children[i].id), label='lower')
            elif i == 1:
                g.edge(str(root.id), str(root.children[i].id), label='upper')
            else:
                g.edge(str(root.id), str(root.children[i].id), label='step')

        elif isinstance(root, peg_nodes.ComprehensionNode):
            if i == 0:
                g.edge(str(root.id), str(root.children[i].id), label='target')
            elif i == 1:
                g.edge(str(root.id), str(root.children[i].id), label='iter_obj')
            else:
                g.edge(str(root.id), str(root.children[i].id), label='if_' + str(i - 2))

        elif isinstance(root, peg_nodes.ListCompNode) or isinstance(root, peg_nodes.SetCompNode) or \
                isinstance(root, peg_nodes.GeneratorExpNode):
            if i == 0:
                g.edge(str(root.id), str(root.children[i].id), label='elem')
            else:
                g.edge(str(root.id), str(root.children[i].id), label='gen_' + str(i - 1))

        elif isinstance(root, peg_nodes.FunctionCall):
            if i == 0:
                g.edge(str(root.id), str(root.children[i].id), label='func')
            else:
                g.edge(str(root.id), str(root.children[i].id), label='arg_' + str(i-1))

        elif isinstance(root, peg_nodes.LambdaNode):
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


def get_nodes(root):

    visited = []
    nodes_list = []
    get_nodes_helper(root, nodes_list, visited)

    return nodes_list


def get_nodes_helper(node, nodes_list, visited):

    if node.id in visited:
        return

    visited.append(node.id)
    nodes_list.append(node)

    for child in node.children:
        get_nodes_helper(child, nodes_list, visited)


def get_non_binded_nodes(root, ctx):
    visited = []
    nodes_list = []
    get_non_binded_nodes_helper(root, nodes_list, visited, ctx)

    return nodes_list


def get_non_binded_nodes_helper(node, nodes_list, visited, ctx):

    if node.id in visited or node.id in [ctx[key].id for key in ctx.keys() if key.startswith('_')]:

        return

    visited.append(node.id)
    nodes_list.append(node)

    for child in node.children:
        get_non_binded_nodes_helper(child, nodes_list, visited, ctx)


from peg_nodes import THETANode, CompareNode, FunctionCall, IdentifierNode
import ast

def is_node_in_two_len_cycle(node):

    for child in node.children:
        if isinstance(child, THETANode):
            return True

    return False


def is_node_forloop_iter(node):
    if len([p for p in node.predecessors if (isinstance(p, CompareNode)) and isinstance(p.ops[0], ast.In)]) > 0:
        if (len([p for p in node.predecessors if (isinstance(p, FunctionCall))
                 and isinstance(p.children[0], IdentifierNode) and p.children[0].name == 'iter'])) > 0:

            return True

    return False

