from staticfg import CFGBuilder
import ast, copy


def copy_propagate(src):

    cfg = CFGBuilder().build_from_src('output', src)

    changed = True

    while changed:

        all_stmts = get_all_stmts(cfg)
        copy_stmts = [s for s in all_stmts.keys() if is_copy_assignement(s)]

        changed = False

        for copy_stmt in copy_stmts:

            # already replaced
            if copy_stmt not in all_stmts.keys():
                continue

            lhs_var, rhs_var = return_copy_assignement_ids(copy_stmt)
            uses_of_lhs_var = [s for s in all_stmts.keys() if stmt_contains_var(s, lhs_var)]

            all_replaced = True

            for use_of_lhs in uses_of_lhs_var:

                block = all_stmts[use_of_lhs]

                # replace if definition and use in same block
                if (block.id == all_stmts[copy_stmt].id and
                block.statements.index(copy_stmt) < block.statements.index(use_of_lhs)):

                    def_idx = block.statements.index(copy_stmt)
                    use_idx = block.statements.index(use_of_lhs)

                    redefs = [s for s in block.statements[def_idx + 1: use_idx] if
                                                            is_stmt_assignement_to_any_of_vars(s, [lhs_var, rhs_var])]

                    if len(redefs) == 0:

                        use_of_lhs_copy = copy.deepcopy(use_of_lhs)
                        replaced_stmt = ReplaceName(lhs_var, rhs_var).visit(use_of_lhs_copy)
                        #recompute idx
                        use_idx = block.statements.index(use_of_lhs)
                        block.statements[use_idx] = replaced_stmt

                        all_stmts[replaced_stmt] = block
                        del all_stmts[use_of_lhs]

                        changed = True

                    else:
                        all_replaced = False

                    continue
            #    if not use_of_lhs in block.statements:
            #        continue

                idx = block.statements.index(use_of_lhs)

            # process if no redefinitions of lhs or rhs between entry of block and use_of_lhs
                redefinitions = [s for s in block.statements[:idx + 1] if
                             is_stmt_assignement_to_any_of_vars(s, [lhs_var, rhs_var])]

                if len(redefinitions) > 0:
                    all_replaced = False
                    continue

                # replace if copy stmt in in_C(block)
                if copy_stmt in in_C(block, cfg):

                    use_of_lhs_copy = copy.deepcopy(use_of_lhs)
                    replaced_stmt = ReplaceName(lhs_var, rhs_var).visit(use_of_lhs_copy)
                    idx = block.statements.index(use_of_lhs)

                    block.statements[idx] = replaced_stmt

                    all_stmts[replaced_stmt] = block
                    del all_stmts[use_of_lhs]

                    changed = True

                else:
                    all_replaced = False

            if all_replaced:

                if copy_stmt in all_stmts.keys():

                    block_of_cpy_stmt = all_stmts[copy_stmt]
                    block_of_cpy_stmt.statements.remove(copy_stmt)

                    del all_stmts[copy_stmt]

    remove_unused_definitions(cfg)

    code_lines = cfg_to_src(cfg)

  #  cfg.build_visual('cfg_output_changed', 'png')

    return code_lines


def get_all_stmts(cfg):

    visited = []
    stmts = {}

    get_all_stmts_helper(cfg.entryblock, visited, stmts)

    return stmts


def get_all_stmts_helper(node, visited, stmts):

    if node.id in visited:
        return

    visited.append(node.id)

    for s in node.statements:
        stmts[s] = node

    for exit in node.exits:
        child = exit.target
        get_all_stmts_helper(child, visited, stmts)


def is_copy_assignement(stmt):

    return isinstance(stmt, ast.Assign) and isinstance(stmt.targets[0], ast.Name) and isinstance(stmt.value, ast.Name)


def paths_between_blocks(b1, b2):

    visited = []
    all_paths_stmts = []
    current_path = []
    paths_between_blocks_helper(b1, b2, current_path, all_paths_stmts, visited)

    return all_paths_stmts

def paths_between_blocks_helper(current_node, b2, current_path, all_paths, visited):

    if visited.count(current_node.id) > 1:
        return

    visited.append(current_node.id)
    current_path.append(current_node)

    if current_node.id == b2.id:

        statements_on_path = [stmt for block in current_path for stmt in block.statements]
        all_paths.append(statements_on_path)

    for exit in current_node.exits:
        child = exit.target
        paths_between_blocks_helper(child, b2, current_path, all_paths, visited)

    current_path.pop()
    visited.remove(current_node.id)

        
def is_loop_header(block):

    if len(block.statements) == 0:
        return False

    return isinstance(block.statements[0], ast.While) or isinstance(block.statements[0], ast.For)


def return_copy_assignement_ids(stmt):

    assert(is_copy_assignement(stmt))

    return (stmt.targets[0].id, stmt.value.id)


def is_stmt_assignement_to_any_of_vars(stmt, var_names):

    for var in var_names:
        if isinstance(stmt, ast.Assign) and isinstance(stmt.targets[0], ast.Name) and stmt.targets[0].id == var:
            return True

    return False


def stmt_reaches_given_point(stmt, p, cfg):

    assert(is_copy_assignement(stmt))

    target_id, value_id = return_copy_assignement_ids(stmt)

    for path in paths_between_blocks(cfg.entryblock, p):

        copy_assignements = [s for s in path if is_copy_assignement(s)]
        if stmt not in copy_assignements:
            return False

        idx = path.index(stmt)

        assignements_to_target_or_value = [s for s in path[idx:] if s != stmt and \
                                           is_stmt_assignement_to_any_of_vars(s, [target_id, value_id])]

        if len(assignements_to_target_or_value) > 0:
            return False

    return True


def stmts_reaching_given_point(stmts, p, cfg):

    return [stmt for stmt in stmts if stmt_reaches_given_point(stmt, p, cfg)]


def in_C(b, cfg):

    all_stmts = [s for s in get_all_stmts(cfg).keys() if is_copy_assignement(s)]
    result = stmts_reaching_given_point(all_stmts, b, cfg)

    for stmt in b.statements:
        if stmt in result:
            result.remove(stmt)

    return result


def out_C(b, cfg):

    all_stmts = [s for s in get_all_stmts(cfg).keys() if is_copy_assignement(s)]
    result = stmts_reaching_given_point(all_stmts, b, cfg)

    return result


class ReplaceName(ast.NodeTransformer):

    def __init__(self, old_name, new_name):
        self.old_name = old_name
        self.new_name = new_name

    def visit_Name(self, node):

        if node.id != self.old_name:
            return node

        return ast.copy_location(ast.Name(id=self.new_name, ctx=node.ctx), node)


def stmt_contains_var(stmt, var):

    if isinstance(stmt, ast.For) or isinstance(stmt, ast.While):
        expression = stmt

    elif isinstance(stmt, ast.If):
        expression = stmt.test

    elif isinstance(stmt, ast.Assign) or isinstance(stmt, ast.Return):
        expression = stmt.value

    else:
        expression = stmt

    for node in ast.walk(expression):
        if isinstance(node, ast.Name) and node.id == var:
            return True

    return False


def remove_unused_definitions(cfg):

    changed = True

    while changed:

        changed = False

        all_stmts = get_all_stmts(cfg)
        all_assignements = [s for s in all_stmts.keys() if isinstance(s, ast.Assign)]

        for assignement in all_assignements:

            target_var = assignement.targets[0].id
            block = all_stmts[assignement]
            idx = block.statements.index(assignement)
            paths_to_endpoint = paths_between_blocks(block, cfg.finalblocks[0])

            stmts_to_next_definition = []

            for p in paths_to_endpoint:
                for s in p[idx + 1:]:
                    if is_stmt_assignement_to_any_of_vars(s, [target_var]):
                        break
                    stmts_to_next_definition.append(s)

            uses_of_target_var = [s for s in stmts_to_next_definition if stmt_contains_var(s, target_var)]

            if len(uses_of_target_var) == 0:

                block.statements.remove(assignement)
                changed = True


def cfg_to_src(cfg):

    visited = []
    code_lines = []
    cfg_to_src_helper(cfg.entryblock, visited, code_lines)

    return code_lines


def cfg_to_src_helper(block, visited, code_lines):

    if block.id in visited:
        return

    visited.append(block.id)

    if len(block.statements) > 0:

        if is_loop_header(block):
            body_lines = []
            cfg_to_src_helper(block.exits[0].target, visited, body_lines)

            block.statements[0].body = body_lines
            code_lines += block.statements

        elif isinstance(block.statements[-1], ast.If):

            true_lines = []
            false_lines = []

            t_visited = list.copy(visited)
            f_visited = list.copy(visited)

            t_successors = blocks_reachable_from(block.exits[0].target, t_visited)
            f_successors = blocks_reachable_from(block.exits[1].target, f_visited)

            same_successors = [succ for succ in t_successors if succ in f_successors]
            same_successors_ids = [succ.id for succ in same_successors]

            visited_with_same_successors = visited + same_successors_ids

            cfg_to_src_helper(block.exits[0].target, visited_with_same_successors, true_lines)
            cfg_to_src_helper(block.exits[1].target, visited_with_same_successors, false_lines)

            visited = [_id for _id in visited_with_same_successors if _id not in same_successors_ids]

            block.statements[0].body = true_lines
            block.statements[0].orelse = false_lines

            code_lines += block.statements

            if len(same_successors) > 0:
                cfg_to_src_helper(same_successors[0], visited, code_lines)

        else:
            code_lines += block.statements

    for exit in block.exits:
        cfg_to_src_helper(exit.target, visited, code_lines)


def blocks_reachable_from(block, visited):

    successors = []
    blocks_reachable_from_helper(block, visited, successors)

    return successors


def blocks_reachable_from_helper(block, visited, successors):

    if block.id in visited:
        return

    visited.append(block.id)
    successors.append(block)

    for exit in block.exits:
        blocks_reachable_from_helper(exit.target, visited, successors)
