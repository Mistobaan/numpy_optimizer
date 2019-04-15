from staticfg import CFG, CFGBuilder, Block, Link
import ast

# Forward flow graph is an acyclic graph created from given control flow graph
class FFGBuilder(object):

    def __init__(self, cfg):
        # create acyclic graph from given control flow graph
        self.nodes_map = {}
        self.loop_headers = []
        self.ffg = self.transform_to_FFG(cfg)

        # helper entry edge
        self.zero_block = Block(max(self.nodes_map.keys()) + 1)
        self.root_edge = Link(self.zero_block, cfg.entryblock)
        self.zero_block.exits.append(self.root_edge)

        # enabling loop initialization
        if self.is_loop_header(cfg.entryblock):
            cfg.entryblock.predecessors.append(self.root_edge)
            pass_stmt = ast.Pass()
            pass_stmt.lineno = 0
            self.zero_block.statements.append(pass_stmt)
            self.nodes_map[self.zero_block.id] = self.zero_block

        assert (len(self.ffg.finalblocks) != 0)

        # multiple return statements case - does not work properly, should be corrected
        if len(self.ffg.finalblocks) > 1:
            fb = Block(max(self.nodes_map.keys()) + 1)
            pass_stmt = ast.Pass()
            pass_stmt.lineno = max([statement.lineno for block in self.ffg.finalblocks
                                    for statement in block.statements])
            fb.statements.append(pass_stmt)
            self.final_block = fb
            self.nodes_map[fb.id] = fb

            for block in self.ffg.finalblocks:
                link = Link(block, fb)
                block.exits.append(link)
                fb.predecessors.append(link)

        else:
            self.final_block = self.ffg.finalblocks[0]

    # method for forward flow graph initialization
    def transform_to_FFG(self, cfg):

        self.transform_to_FFG_helper(cfg.entryblock, self.nodes_map, [])

        return cfg

    def transform_to_FFG_helper(self, block, nodes_map, visited):

        if block.id in visited:
            return

        visited.append(block.id)
        nodes_map[block.id] = block

        # remove cycles
        if self.is_loop_header(block) and block.id >= 0:

            self.loop_headers.append(block.id)

            for edge in block.predecessors:
                if self.is_back_edge(edge):

                    source = edge.source
                    source.exits.remove(edge)

                    # create a copy of each loop header node
                    id_of_copy = self.get_id_of_copy_from_original(block.id)

                    if id_of_copy not in nodes_map.keys():
                        new_block = Block(id_of_copy)
                        new_block.statements = block.statements
                        nodes_map[id_of_copy] = new_block
                        self.loop_headers.append(id_of_copy)

                    # reconnect all back edges pointing to original loop headers
                    # to point to their copies
                    current_block = nodes_map[id_of_copy]
                    new_edge = Link(source, current_block, exitcase=edge.exitcase)
                    current_block.predecessors.append(new_edge)
                    source.exits.append(new_edge)

            # remove old back edges
            block.predecessors = [edge for edge in block.predecessors if not self.is_back_edge(edge)]

        # recursively visit all the blocks of the control flow graph
        for exit in block.exits:
            self.transform_to_FFG_helper(exit.target, nodes_map, visited)

    def get_id_of_copy_from_original(self, original_id):

        # defined for loop headers only
        assert (self.is_loop_header(self.nodes_map[original_id]))

        return -original_id - 1

    def get_id_of_original_from_copy(self, copy_id):

        original_id = -copy_id - 1

        # defined for loop header copies only
        assert (self.is_loop_header(self.nodes_map[original_id]))

        return original_id

    @staticmethod
    def is_loop_header(block):

        if block.is_empty():
            return False

        fst_stmt = block.statements[0]
        return isinstance(fst_stmt, ast.For) or isinstance(fst_stmt, ast.While)

    @staticmethod
    def is_back_edge(edge):

        source_lineno = edge.source.at()
        target_lineno = edge.target.at()

        if source_lineno == None:
            return False

        return target_lineno <= source_lineno

    def is_node_in_loop(self, node, loop_header_node):

        return loop_header_node in self.node_loops(node)

    def compute_break_edges(self, loop_header_node):

        # break edges of copy of a loop header node are same as original's
        if loop_header_node.id < 0:
            original_id = self.get_id_of_original_from_copy(loop_header_node.id)
            return self.compute_break_edges(self.nodes_map[original_id])

        edges = []

        # for each node inside the loop (or the loop header itself)
        for inside_node_id, inside_node in self.nodes_reachable_from(loop_header_node).items():
            if self.is_node_in_loop(inside_node, loop_header_node) or inside_node == loop_header_node:

                for exit in inside_node.exits:

                    exit_target_id = exit.target.id if exit.target.id >= 0 \
                        else self.get_id_of_original_from_copy(exit.target.id)
                    exit_target_node = self.nodes_map[exit_target_id]

                    # if source node of the exit edge is in the loop and target is out
                    if not self.is_node_in_loop(exit_target_node, loop_header_node) and \
                            exit_target_node != loop_header_node:
                        edges.append(exit)

        return edges

    # nodes in graph reachable from the given node (including itself)
    def nodes_reachable_from(self, node):

        nodes_map = {}
        self.nodes_reachable_from_helper(node, nodes_map, [])

        return nodes_map

    def nodes_reachable_from_helper(self, start_node, nodes_map, visited):

        if start_node.id in visited:
            return

        nodes_map[start_node.id] = start_node
        visited.append(start_node.id)

        for edge in start_node.exits:
            self.nodes_reachable_from_helper(edge.target, nodes_map, visited)

    # edges in graph reachable from the given edge (including itself)
    def edges_reachable_from(self, edge):

        edges_list = []
        self.edges_reachable_from_helper(edge, edges_list)

        return edges_list

    def edges_reachable_from_helper(self, start_edge, edges_list):

        if start_edge in edges_list:
            return

        edges_list.append(start_edge)

        for edge in start_edge.target.exits:
            self.edges_reachable_from_helper(edge, edges_list)

    def edges_from_edge_to_node(self, source_edge, target_node):

        edges_list = self.edges_reachable_from(source_edge)

        if target_node == None:
            return edges_list

        result = [e for e in edges_list if target_node.id in self.nodes_reachable_from(e.target).keys()]

        return result

    # returns loop header nodes of loops that contain the given node,
    # resulting list is ordered by nest depth decreasingly (deeper loops first)
    def node_loops(self, node):

        loops = []

        # loop header copies are computed this way
        if node.id < 0:
            original_id = self.get_id_of_original_from_copy(node.id)
            original_node = self.nodes_map[original_id]
            self.node_loops_helper(original_node, loops)

            loops = [original_node] + loops

        else:
            self.node_loops_helper(node, loops)

            if self.is_loop_header(node):
                loops = [node] + loops

        return loops

    def node_loops_helper(self, node, loops):

        for current_node_id, current_node in self.nodes_map.items():

            if self.is_loop_header(current_node) and current_node.at() < node.at() and \
                    self.get_id_of_copy_from_original(current_node.id) in self.nodes_reachable_from(node):

                if current_node not in loops:
                    loops.append(current_node)
                    # recursively compute loops that contain current loop
                    self.node_loops_helper(current_node, loops)

    def compute_loop_condition(self, loop_header_node):

        assert (self.is_loop_header(loop_header_node))

        loop_statement = loop_header_node.statements[0]

        if isinstance(loop_statement, ast.For):
            iterator = loop_statement.iter
            var = loop_statement.target
            return ast.Compare(left=var, ops=[ast.In()], comparators=[iterator])

        if isinstance(loop_statement, ast.While):
            return loop_statement.test

        return None

    # computes the dominator node of given edge set in forward flow graph
    def least_dominator_through(self, source_edge, edge_set):

        edges_reachable_from_source = self.edges_reachable_from(source_edge)

        is_reachable_from_source = lambda edge: edge in edges_reachable_from_source

        if not all(map(is_reachable_from_source, edge_set)):
            return None

        for edge in source_edge.target.exits:

            dominator = self.least_dominator_through(edge, edge_set)
            if dominator != None:
                return dominator

        if source_edge in edge_set:
            return source_edge.source
        else:
            return source_edge.target

    def render(self, filename='FFG', extension='png'):

        self.ffg.build_visual(filename, extension)
