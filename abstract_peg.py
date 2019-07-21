import ast
import astor
from ffg import FFGBuilder
from staticfg import CFGBuilder


class APEGNodeBase(object):

    def __init__(self, _id, children=[]):
        self.id = _id
        self.children = children


class APEGNode(APEGNodeBase):

    def __init__(self, _id, children, statements):
        super(APEGNode, self).__init__(_id, children)
        self.statements = statements

    def __str__(self):
        result = 'SE_Node' + ' ' + str(self.id) + '\n'
        statements_str = map(lambda x: astor.to_source(x)[:astor.to_source(x).find('\n')], self.statements)

        for stmt in list(statements_str)[:1]:
            result += stmt

        return result


class PHI_APEGNode(APEGNodeBase):

    def condition_node(self):
        return self.children[0]

    def true_node(self):
        return self.children[1]

    def false_node(self):
        return self.children[2]

    def __str__(self):
        return 'PHI_Node' + ' ' + str(self.id)


class THETA_APEGNode(APEGNodeBase):

    def initial_node(self):
        return self.children[0]

    def iteration_node(self):
        return self.children[1]

    def __str__(self):
        return 'THETA_Node' + ' ' + str(self.id)


class Condition_APEGNode(APEGNode):

    def boolean_expression(self):
        return self.statements[0]

    def __str__(self):
        return 'Cond_Node' + str(self.id) + '\n' + (astor.to_source(self.boolean_expression())
                                                    if self.boolean_expression() is None
                                                    else 'no_expression')


class Pass_APEGNode(APEGNodeBase):

    def break_condition(self):
        return self.children[0]

    def __str__(self):
        return 'Pass_Node' + ' ' + str(self.id)


class Eval_APEGNode(APEGNodeBase):

    def theta_node(self):
        return self.children[0]

    def pass_node(self):
        return self.children[1]

    def __str__(self):
        return 'Eval_Node' + ' ' + str(self.id)


class True_APEGNode(APEGNodeBase):

    def __str__(self):
        return 'True_Node' + ' ' + str(self.id)


class False_APEGNode(APEGNodeBase):

    def __str__(self):
        return 'False_Node' + ' ' + str(self.id)


# Abstract Program Expression Graph
class APEG(object):

    def __init__(self, ffg):

        self.ffg = ffg
        self.nodes_map = {}
        self.conditions_map = {}
        self.ffg_to_apeg_node_id = {}
        self.current_id = 0

        self.apeg_root = self.transform_to_APEG()

        nodes = self.nodes_reachable_from(self.apeg_root, [])

        for node in nodes:
            if isinstance(node, Eval_APEGNode):

                val = node.children[0]

                if isinstance(val.statements[0], ast.For):

                    theta_node = val.children[0]
                    init_node = theta_node.children[0]
                    iter_node = theta_node.children[1]

                    init_stmt, iter_stmt = self.extract_forloop_init_and_iter_stmt(val.statements[0])

                    if isinstance(init_node, APEGNode) and not self.is_loop_header(init_node):
                        init_node.statements = [init_stmt] + init_node.statements
                    else:
                        new_node = APEGNode(self.compute_id(), children=[init_node], statements=[init_stmt])
                        theta_node.children[0] = new_node
                        self.nodes_map[self.current_id] = new_node

                    if isinstance(iter_node, APEGNode) and not self.is_loop_header(iter_node):
                        iter_node.statements.append(iter_stmt)
                    else:
                        new_node = APEGNode(self.compute_id(), children=[iter_node], statements=[iter_stmt])
                        theta_node.children[1] = new_node
                        self.nodes_map[self.current_id] = new_node

    def compute_id(self):

        self.current_id += 1
        return self.current_id

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


    def transform_to_APEG(self):

        for node_id, node in self.ffg.nodes_map.items():

            # duplicate loop headers node are excluded
            if node_id < 0:
                continue

            new_node = APEGNode(self.compute_id(), children=[], statements=node.statements)
            self.nodes_map[self.current_id] = new_node
            self.ffg_to_apeg_node_id[node_id] = self.current_id

            if len(node.exits) > 0:

                condition = node.exits[0].exitcase
                self.conditions_map[self.current_id] = Condition_APEGNode(self.current_id, [], [condition])

                if isinstance(node.statements[-1], ast.If):
                    new_node.statements = node.statements[:-1]

                    if len(new_node.statements) == 0:
                        stmt = ast.Pass()
                        new_node.statements.append(stmt)

        for node_id, node in self.ffg.nodes_map.items():

            # duplicate loop headers node are excluded
            if node_id < 0:
                continue

            apeg_node_id = self.ffg_to_apeg_node_id[node_id]
            apeg_node = self.nodes_map[apeg_node_id]

            node_input = self.compute_inputs(node)
            if node_input != None:
                apeg_node.children.append(node_input)

        root_id = self.ffg_to_apeg_node_id[self.ffg.final_block.id]
        root = self.nodes_map[root_id]

        return root

    def compute_inputs(self, node):

        in_edges = [edge for edge in node.predecessors if not edge.source.is_empty()]

        if len(in_edges) == 0:
            return None

        # function that maps edge from FFG node to APEG node corresponding to source of the edge
        value_fn = lambda e: self.nodes_map[self.ffg_to_apeg_node_id[e.source.id]]
        loops_of_n = self.ffg.node_loops(node)

        result = self.decide(self.ffg.root_edge, in_edges, value_fn, loops_of_n, node)

        # if n is a loop header (original), create a theta node
        if self.ffg.is_loop_header(node) and node.id >= 0:
            i = len(loops_of_n)  # i is a nest depth
            id_of_copy = self.ffg.get_id_of_copy_from_original(node.id)
            copy_node = self.ffg.nodes_map[id_of_copy]

            iteration_node = self.compute_inputs(copy_node)
            theta = THETA_APEGNode(self.compute_id(), children=[result, iteration_node])

            result = theta
            self.nodes_map[self.current_id] = result

        return result

    def decide(self, source_edge, edge_set, value_fn, loop_set, node=None):

        if len(edge_set) == 0:
            ffg_node_id = source_edge.source.id if source_edge.source.id > 0 \
                else self.ffg.get_id_of_copy_from_original(source_edge.source.id)

            apeg_node_id = self.ffg_to_apeg_node_id[ffg_node_id]
            return self.nodes_map[apeg_node_id]

        d = self.ffg.least_dominator_through(source_edge, edge_set)

        assert (d != None)
        loops_of_d = self.ffg.node_loops(d)

        # if all loops containing d are in loop_set
        if all(map(lambda l: l in loop_set, loops_of_d)):

            # if all edges maps to the same value, return that value
            if len(set(map(value_fn, edge_set))) == 1:
                return value_fn(edge_set[0])

            if len(d.exits) == 1:
                d_edge = d.exits[0]
                edges_reachable_from_d = self.ffg.edges_from_edge_to_node(d_edge, node)
                edges_reachable_from_d.remove(d_edge)
                return self.decide(d_edge, edges_reachable_from_d, value_fn, loop_set, node)

            # in other case, d's last statement is a branch
            true_edge = d.exits[0]
            false_edge = d.exits[1]

            edges_reachable_from_true = self.ffg.edges_from_edge_to_node(true_edge, node)
            edges_reachable_from_true.remove(true_edge)
            edges_reachable_from_false = self.ffg.edges_from_edge_to_node(false_edge, node)
            edges_reachable_from_false.remove(false_edge)

            t = self.decide(true_edge, edges_reachable_from_true, value_fn, loop_set, node)
            f = self.decide(false_edge, edges_reachable_from_false, value_fn, loop_set, node)

            apeg_node_id = self.ffg_to_apeg_node_id[d.id]
            cond = self.conditions_map[apeg_node_id]

            phi_node = PHI_APEGNode(self.compute_id(), children=[cond, t, f])
            self.nodes_map[self.current_id] = phi_node

            return phi_node

        else:

            # compute the outermost loop from loops_of_d that is not in loop_set
            l = None
            for loop in loops_of_d[::-1]:
                if loop not in loop_set:
                    l = loop
                    break

            assert (l != None)

            # nest depth
            i = len(self.ffg.node_loops(l))

            break_edges = self.ffg.compute_break_edges(l)
            break_condition = self.compute_break_condition(l, break_edges, loop_set + [l])
            val = self.decide(source_edge, edge_set, value_fn, loop_set + [l])

            pass_apeg_node = Pass_APEGNode(self.compute_id(), children=[break_condition])
            self.nodes_map[self.current_id] = pass_apeg_node

            eval_apeg_node = Eval_APEGNode(self.compute_id(), children=[val, pass_apeg_node])
            self.nodes_map[self.current_id] = eval_apeg_node

            return eval_apeg_node

    def compute_break_condition(self, l, break_edges, loop_set):

        # copy of loop header node in the acyclic graph
        l_copy_id = self.ffg.get_id_of_copy_from_original(l.id)
        l_copy = self.ffg.nodes_map[l_copy_id]

        # union of break edges and back edges
        all_edges = break_edges + l_copy.predecessors

        value_fn = lambda e: True_APEGNode(self.compute_id()) if e in break_edges \
            else False_APEGNode(self.compute_id())

        result = self.simplify(self.decide(self.ffg.root_edge, all_edges, value_fn, loop_set))

        return result


    def simplify(self, phi_node):

        if not (isinstance(phi_node, PHI_APEGNode)):
            return phi_node

        cond = phi_node.children[0]
        t = phi_node.children[1]

        result = cond if isinstance(t, True_APEGNode) \
            else Condition_APEGNode(phi_node.id, [],
                                    [ast.UnaryOp(op=ast.Not(), operand=cond.statements[0])])

        return result


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

        iter_call = ast.Call(func=ast.Name(id='iter', ctx=ast.Load()), args=[iterator], keywords=[])
        next_iter_call = ast.Call(func=ast.Name(id='next', ctx=ast.Load()), args=[iter_call], keywords=[])
        loop_var_assign = ast.Assign(targets=[loop_var], value=next_iter_call)

        astor.to_source(loop_var_assign)

        next_expression = ast.Call(func=ast.Name(id='next', ctx=ast.Load()), args=[loop_var], keywords=[])
        next_stmt = ast.Assign(targets=[loop_var], value=next_expression)

        return loop_var_assign, next_stmt

    def is_loop_header(self, node):

        if len(node.statements) == 0:
            return False

        if isinstance(node.statements[0], ast.For) or isinstance(node.statements[0], ast.While):
            return True

        return False


def compute_apeg_from_source(src, name):

    cfg = CFGBuilder().build_from_src(name=name, src=src)
    function_def = cfg.entryblock.statements[0]

    if isinstance(function_def, ast.FunctionDef):
        name = function_def.name
        ffg = FFGBuilder(cfg.functioncfgs[name])

    else:
        ffg = FFGBuilder(cfg)
        function_def = None

    apeg = APEG(ffg)

    return apeg, function_def