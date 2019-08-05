from peg_nodes import THETANode, EvalNode, PassNode, NPArrayNode
import re
from peg_builder import get_nodes


def node_instance(node):

    id_str = '(id ' + str(node.id) + ')'
    type_str = '(type ' + node.type_name().split('_')[0] + ')'
    args_str = '(args ' + node.type_name().split('_')[1] + ')'
    children_str = '(children ' + ' '.join([child.eq_class for child in node.children]) + ')'
    eq_class_str = '(eq-class ' + node.eq_class + ')'
    loop_variance_indices_str = '(loop-variance-indices ' + \
                                ' '.join([str(idx) for idx in node.loop_variance_indices]) + ')'

    slot_strs = [id_str, eq_class_str, type_str, args_str, children_str, loop_variance_indices_str]

    if node.compute_expr_type() != 'unknown':
        expr_type_str = '(expr-type ' + node.compute_expr_type() + ')'
        slot_strs.append(expr_type_str)

    if isinstance(node, THETANode) or isinstance(node, EvalNode):
        slot_strs.append('(loop-depth ' + str(node.loop_depth) + ')')

    if isinstance(node, NPArrayNode) and node.shape != None:
        slot_strs.append('(shape ' + ' '.join([str(dim) for dim in node.shape]) + ')')

    return '(make-instance id_' + str(node.id) + ' of node ' + ' ' + ' '.join(slot_strs) + ')'


def node_lhs_pattern(node, bindings, root_var):

    assert (root_var == 'lhs' or root_var == 'rhs')

    create_id_var = lambda _id: '?var-' + _id

    create_eq_class_var = lambda eq_class: ('?var-' + eq_class) if re.search('class', eq_class) != None else eq_class
    type_info = node.type_name().split('_')

    id_str = '(id ' + create_id_var(str(node.id)) + ')'
    type_str = '(type ' + type_info[0] + ')' if not (type_info[0] == 'PEGNode' or node.eq_class.find('class') < 0)\
                                            else '(type ?type_' + str(node.id) + ')'

    if type_info[0] == 'PEGNode' or node.eq_class.find('class') < 0:
        children_str = '(children $?ch' + '_' + str(node.id) + ')'
    else:
        children_str = '(children ' + ' '.join([create_eq_class_var(child.eq_class) for child in node.children]) + ')'

    # case of leaf nodes, with token arg
    if node.id in bindings.keys() or node.eq_class.find('class') < 0:
        args_str = '(args ' + ('$?arg_' + str(node.id)) + ')'
    else:
        args_str = '(args ' + type_info[1] + ')'

    eq_class_str = '(eq-class ' + create_eq_class_var(node.eq_class) + ')'
    loop_variance_indices_str = '(loop-variance-indices ' + ('$?indices-' + str(node.id)) + ')'
    slot_strs = [id_str, eq_class_str, type_str, args_str, children_str, loop_variance_indices_str]

    if node.compute_expr_type() != 'unknown':
        expr_type_str = '(expr-type ' + node.compute_expr_type() + ')'
        slot_strs.append(expr_type_str)

    if isinstance(node, THETANode) or isinstance(node, EvalNode):
        slot_strs.append('(loop-depth ' + '?loop-d-' + str(node.id) + ')')

    if isinstance(node, NPArrayNode) and node.shape != None:
        slot_strs.append('(shape ' + ' '.join([str(dim) for dim in node.shape]) + ')')

    return '(object (is-a node) ' + ' '.join(slot_strs) + ')'


def node_rhs_assertion(node, bindings, theta_node_children_strs):

    _id = (('?var-' + str(node.id)) if node.id in bindings.keys() else ('(transform-id ' + str(node.id)) + ')')
    id_str = '(id ' + _id + ')'

    type = node.type_name().split('_')[0]
    type_str = '(type ' + type + ')'

    create_eq_class_var = lambda eq_class: ('?var-' + eq_class) if re.search('class', eq_class) != None else eq_class

    children_eq_classes = [(create_eq_class_var(child.eq_class)) if child.id in bindings.keys()
                           else child.eq_class for child in node.children]

    children_eq_classes = [('?var-' + child.eq_class) for child in node.children]

    children_str = '(children ' + \
                   ' '.join(children_eq_classes) + ')' if not isinstance(node, THETANode) else ''

    eq_class = ('(transform-class-id ' + node.eq_class + ')') if not node.id in bindings.keys() \
                                    else create_eq_class_var(node.eq_class)
    eq_class_str = '(eq-class ' + eq_class + ')'

    args = str(node.type_name().split('_')[1])
    args_str = '(args ' + args + ')'

    loop_depth_str = ''
    if isinstance(node, THETANode) or isinstance(node, EvalNode):
        loop_depth_str = '(loop-depth ' + str(node.loop_depth) + ')'

    shape_str = ''
    if isinstance(node, NPArrayNode) and node.shape != None:
        shape_str = '(shape ' + ' '.join([str(dim) for dim in node.shape]) + ')'

    instance_name = '(string-to-field (str-cat "_id" (str-cat (transform-id ' + str(node.id) + '))))'

    expr_type_str = '(expr-type ' + node.compute_expr_type() + ')'


    if isinstance(node, THETANode):
        theta_node_children_strs.append(
            ('(send (nth$ 1 (find-instance ((?n node)) (= ?n:id ' + _id + '))) put-children (create$ ' + \
                                                    (' '.join(children_eq_classes)) + '))'))


    bind_class = '(bind ?var-' + node.eq_class + ' ' + eq_class + ')'
    assertion = '(make-instance ' + instance_name + ' of node ' + id_str + ' ' + eq_class_str + ' ' + expr_type_str + \
                                    ' ' + type_str + ' ' + args_str + ' ' + loop_depth_str + ' ' + \
                                    shape_str + ' ' + children_str + ')'
    update_instances_counter = '(bind ?*created-instances-counter* (+ ?*created-instances-counter* 1))'

    assertion = bind_class + ' ' + assertion + ' ' + update_instances_counter

    check_existance = '(bind ?existance-val (already-exists ' + type + ' ' + '(create$ ' + args + ') ' + \
                                '(create$ ' + ' '.join(children_eq_classes) + ')' + '))'

    conditional_assertion = '(if (eq ?existance-val FALSE) then ' + \
                            assertion + ' else (bind ?var-' + node.eq_class + ' ?existance-val))'

    if isinstance(node, THETANode):
        return assertion

    return check_existance + conditional_assertion


def clips_node_to_node_info(clips_node):

    pattern_str = r"\(id (.+)\) \(eq-class (.+)\) \(type (.+)\) \(args ?(.+)?\) \(children ?(.+)?\)"
    pattern_str += r" \(loop-variance-indices ?(.+)?\) \(loop-depth (-?\d+)\) "
    pattern = re.compile(pattern_str)
    search_obj = pattern.search(clips_node)

    if search_obj == None:
        return None

    _id = search_obj.groups()[0]
    eq_class = search_obj.groups()[1]
    type_name = search_obj.groups()[2]
    args = search_obj.groups()[3]
    children = (search_obj.groups()[4] if search_obj.groups()[4] != None else '').split()
    loop_depth = search_obj.groups()[6]

    return [_id, eq_class, type_name, args, loop_depth] + children


def create_rule(peg):


    assert(peg.axiom_mode)

    lhs = peg_to_condition(peg, 'lhs')

    for inv_node_id, loop_id in peg.invariants.items():
        # move to clips constructs as predicate
        lhs += '(test (and (not (member$ -1 $?indices-' + str(inv_node_id) + ')) (not (member$ ?loop-d-' \
               + str(loop_id) + '  $?indices-' + str(inv_node_id) + '))))\n'

    rhs = peg_to_action(peg)
    clips_construct = '(defrule ' + peg.ctx['axiom_name'].token.s + '\n' + lhs + '\n=>\n' + rhs + ')'

    return clips_construct


def peg_to_condition(peg, root_var):

    visited = []
    clips_construct = []

    peg_to_condition_helper(peg.ctx[root_var], visited, clips_construct, peg.bindings, root_var)
    return '\n'.join(clips_construct)


def peg_to_condition_helper(node, visited, clips_construct, bindings, root_var):

    if node.id in visited:
        return

    visited.append(node.id)
    clips_construct.append(node_lhs_pattern(node, bindings, root_var))

    for child in node.children:
        peg_to_condition_helper(child, visited, clips_construct, bindings, root_var)


def peg_to_instances(peg):

    assert(peg.axiom_mode == False)

    visited = []
    clips_construct = []

    peg_to_instances_helper(peg.ctx['retvar'], visited, clips_construct)
    clips_construct.append('(assert (current-id (value ' + str(peg.current_id + 3) + ')))')

    return '\n'.join(clips_construct)


def peg_to_instances_helper(node, visited, clips_construct):

    if node.id in visited:
        return

    visited.append(node.id)
    clips_construct.append(node_instance(node))

    for child in node.children:
        peg_to_instances_helper(child, visited, clips_construct)


def peg_to_action(peg):

    visited = []
    clips_construct = []
    theta_node_children_strs = []

    peg_to_action_helper(peg.ctx['rhs'], visited, clips_construct, peg.bindings, theta_node_children_strs)

    for s in theta_node_children_strs:
        clips_construct.append(s)

    eq_left = '?var-' + peg.ctx['lhs'].eq_class
    eq_right = '?var-' + peg.ctx['rhs'].eq_class
    rl_assertion = '(assert (equal-classes (fst ' + eq_right + ') (snd ' + eq_left + ')))'
    rl_assertion += ' (printout output-file ' + eq_right + '" "' + eq_left + '" ")'
    lr_assertion = '(assert (equal-classes (fst ' + eq_left + ') (snd ' + eq_right + ')))'
    lr_assertion += ' (printout output-file ' + eq_left + '" "' + eq_right + '" ")'
    equality_stmt = '(if (eq (is-negative-id ' + eq_right + ') FALSE) then ' + rl_assertion + \
                    ' else ' + lr_assertion + ')'

    axiom_name_stmt = '(printout output-file ' + peg.ctx['axiom_name'].token.s + ' " ")'

    lhs_nodes = get_nodes(peg.ctx['lhs'])
    rhs_nodes = get_nodes(peg.ctx['rhs'])

    lhs_printout = '(printout output-file "l("'+ '" "'.join([('?var-' + str(l.id)) for l in lhs_nodes]) + '") ")'
    rhs_printout = '(printout output-file "r("' + \
                    '" "'.join([('(transform-id ' + \
                                 str(r.id) + ')') if not r.id in peg.bindings.keys() else ('?var-' + str(r.id)) \
                                                     for r in rhs_nodes]) + '")" crlf)'

    clips_construct.append('(if (neq ' + eq_left + ' ' + eq_right + ') then ' + \
                           axiom_name_stmt + ' ' + equality_stmt + ' ' + lhs_printout + ' ' + rhs_printout + ')')

    clips_construct.append('(if (> ?*created-instances-counter* 0) then (do-for-fact ((?curr-id current-id)) TRUE' + \
                                '(modify ?curr-id (value (+ (fact-slot-value ?curr-id value) ' + \
                                str(peg.current_id + 1) + '))))))')

    clips_construct.append('(bind ?*created-instances-counter* 0)')

    return '\n'.join(clips_construct)


def peg_to_action_helper(node, visited, clips_construct, bindings, theta_node_children_strs):

    if node.id in visited:
        return

    visited.append(node.id)

    if isinstance(node, THETANode) and node.id not in bindings.keys():
        current_stmt = node_rhs_assertion(node, bindings, theta_node_children_strs)
        clips_construct.append(current_stmt)

    for child in node.children:
        peg_to_action_helper(child, visited, clips_construct, bindings, theta_node_children_strs)

    if not isinstance(node, THETANode) and node.id not in bindings.keys():
        current_stmt = node_rhs_assertion(node, bindings, theta_node_children_strs)
        clips_construct.append(current_stmt)


import ast, peg_nodes

def node_from_type_info(_id, eq_class, type_name, args, loop_depth):

    if args != None:

        if type_name == 'BinOpNode' or type_name == 'UnaryOpNode':

            op = getattr(ast, args)()
            node = getattr(peg_nodes, type_name)(_id, op, [])
            node.eq_class = eq_class
            return node

        elif type_name == 'CompareNode':

            args = args.split()
            ops = [getattr(ast, arg)() for arg in args]
            node = getattr(peg_nodes, type_name)(_id, ops, [])
            node.eq_class = eq_class
            return node

        elif type_name == 'AttributeNode':

            attr = args
            node = getattr(peg_nodes, type_name)(_id, attr, [])
            node.eq_class = eq_class
            return node

        elif type_name == 'THETANode':

            var_name = args
            loop_depth = int(loop_depth)
            node = getattr(peg_nodes, type_name)(_id, [], loop_depth, var_name)
            node.eq_class = eq_class
            return node

        elif type_name == 'IdentifierNode':

            name = args
            node = getattr(peg_nodes, type_name)(_id, name)
            node.eq_class = eq_class
            return node

        else:

            token = ast.parse(args).body[0].value
            node = getattr(peg_nodes, type_name)(_id, token)
            node.eq_class = eq_class
            return node

    node = getattr(peg_nodes, type_name)(_id, [])
    node.eq_class = eq_class

    if isinstance(node, EvalNode) or isinstance(node, PassNode):
        node.loop_depth = int(loop_depth)

    return node


def equalivalent_classes_peg(peg, conditional_side=False):

    assert(peg.axiom_mode)

    lhs_eq_class = '?var-' + peg.ctx['lhs'].eq_class if peg.ctx['lhs'].eq_class.find('class') >= 0 \
                                                    else peg.ctx['lhs'].eq_class
    rhs_eq_class = '?var-' + peg.ctx['rhs'].eq_class if ((peg.ctx['rhs'].id in peg.bindings.keys() or conditional_side)
                                                         and  peg.ctx['rhs'].eq_class.find('class') >= 0) \
                                                    else peg.ctx['rhs'].eq_class

    return lhs_eq_class, rhs_eq_class


def equality_construct_from_pair(left, right):

    return '(equal-classes (fst ' + left + ') (snd ' + right + '))'


def get_lhs_rhs_node_ids_from_line(line):

    l_pattern = re.search("l\(((-?\d+\s?)*)\)", line)
    r_pattern = re.search("r\(((-?\d+\s?)*)\)", line)

    axiom_name = line.split()[0]

    left_ids = [int(n_id) for n_id in l_pattern.groups()[0].split()]
    right_ids = [int(n_id) for n_id in r_pattern.groups()[0].split()]

    return axiom_name, left_ids, right_ids