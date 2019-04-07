from peg import PEGNode, BinOpNode, CompareNode, BoolOpNode, BytesNode, NumericNode, ListNode
from peg import LiteralNode, StringNode, DictNode, TupleNode, UnaryOpNode, SetNode, FunctionCall
from peg import THETANode, PHINode, EvalNode, PassNode, Param, TemporaryNode
from peg import PEG
import copy
import ast
import astor

class StmtNode(PEGNode):

    def __init__(self, _id, children_keys, children, stmt, output_vars):
        self.id = _id
        self.children_keys = children_keys
        self.children = children
        self.stmt = stmt
        self.output_vars = output_vars


class LoopNode(PEGNode):

    def __init__(self, _id, children_keys, children, body, output_vars, condition):
        self.id = _id
        self.children_keys = children_keys
        self.children = children
        self.body = body
        self.output_vars = output_vars
        self.condition = condition
        self.additional_ids = []
        self.stmt = None
        self.predecessor = None
        self.stmt_ret = None
        self.stmt_cond = None
        self.break_condition = None

    def compute_stmt(self, stmt_iter):
        loop_stmt = self.stmt_cond + [ast.While(test=self.break_condition,
                                                body=(stmt_iter + self.stmt_cond), orelse=[])] + self.stmt_ret

        return loop_stmt


class BranchNode(PEG):

    def __init__(self, _id, children_keys, children, true_branch, false_branch, output_vars, condition):
        self.id = _id
        self.children_keys = children_keys
        self.children = children
        self.true_branch = true_branch
        self.false_branch = false_branch
        self.output_vars = output_vars
        self.condition = condition
        self.additional_ids = []
        self.true_stmt = None
        self.false_stmt = None
        self.predecessor = None
        self.stmt_cond = None
        self.predicate = None

    def compute_stmt(self, true_stmt, false_stmt):
        branch_stmt = self.stmt_cond + [ast.If(test=ast.Name(id=self.predicate, ctx=ast.Load()),
                                               body=true_stmt, orelse=false_stmt)]

        return branch_stmt


def replace(var, name_bindings):
    if isinstance(var, ast.Name) and var.id in name_bindings.keys():
        return name_bindings[var.id]

    return var


def remove_occurences_of_updated_value(var, name_bindings):
    keys_to_remove = []

    for key in name_bindings.keys():
        if contains_var(var, name_bindings[key]):
            keys_to_remove.append(key)

    for key in keys_to_remove:
        del name_bindings[key]


def contains_var(var, expr):


    if isinstance(expr, ast.Name):
        return expr.id == var

    if isinstance(expr, ast.UnaryOp):
        return contains_var(var, expr.operand)

    if isinstance(expr, ast.BinOp):
        return contains_var(var, expr.left) or contains_var(var, expr.right)

    if isinstance(expr, ast.Call):
        return any(map(lambda arg: contains_var(var, arg), expr.args))

    if isinstance(expr, ast.Compare):
        return contains_var(var, expr.left) or any(map(lambda e: contains_var(var, e), expr.comparators))

    return False


def forward_propagate(stmt, name_bindings):
    if isinstance(stmt, ast.Return):
        value = replace(stmt.value, name_bindings)
        return ast.Return(value=value)

    assert (isinstance(stmt, ast.Assign))

    target = stmt.targets[0]
    value = stmt.value

    if isinstance(value, ast.BinOp):
        left = replace(value.left, name_bindings)
        right = replace(value.right, name_bindings)
        value = ast.BinOp(left=left, op=value.op, right=right)

    if isinstance(value, ast.Compare):
        left = replace(value.left, name_bindings)
        comparators = list(map(lambda c: replace(c, name_bindings), value.comparators))
        value = ast.Compare(left=left, ops=value.ops, comparators=comparators)

    elif isinstance(value, ast.UnaryOp):
        operand = replace(value.operand, name_bindings)
        value = ast.UnaryOp(op=value.op, operand=operand)

    elif isinstance(value, ast.Name):
        value = replace(value, name_bindings)

    remove_occurences_of_updated_value(target.id, name_bindings)
    name_bindings[target.id] = value

    return ast.Assign(targets=[target], value=value)


def basic_block_forward_propagation(sentence, name_bindings):
    for i in range(len(sentence)):

        if isinstance(sentence[i], ast.Assign) or isinstance(sentence[i], ast.Return):
            new_stmt = forward_propagate(sentence[i], name_bindings)
            sentence[i] = new_stmt

        if isinstance(sentence[i], ast.While):
            test = sentence[i].test
            body = sentence[i].body

            body_name_bindings = {}
            basic_block_forward_propagation(body, body_name_bindings)

            # new_test = replace(test.operand, body_name_bindings)
            # sentence[i].test = new_test

            name_bindings = {}

        if isinstance(sentence[i], ast.If):
            test = sentence[i].test

            new_test = replace(test, name_bindings)
            sentence[i].test = new_test

            true_branch = sentence[i].body
            false_branch = sentence[i].orelse

            basic_block_forward_propagation(true_branch, {})
            basic_block_forward_propagation(false_branch, {})

            name_bindings = {}


def sentence_rhs_expressions(sentence):
    if len(sentence) == 0:
        return []

    if isinstance(sentence[0], ast.Assign) or isinstance(sentence[0], ast.Return):
        value = sentence[0].value
        return sentence_rhs_expressions(sentence[1:]) + [value]

    if isinstance(sentence[0], ast.While):
        test = sentence[0].test
        return [test] + sentence_rhs_expressions(sentence[0].body) + sentence_rhs_expressions(sentence[1:])

    if isinstance(sentence[0], ast.If):
        test = sentence[0].test
        return [test] + sentence_rhs_expressions(sentence[0].body) + \
               sentence_rhs_expressions(sentence[0].orelse) + sentence_rhs_expressions(sentence[1:])


def remove_useless_assignements(assignements_to_remove, sentence, rhs_expressions):
    for stmt in sentence:

        if isinstance(stmt, ast.Assign):

            target = stmt.targets[0]

            if not any(map(lambda expr: contains_var(target.id, expr), rhs_expressions)):
                assignements_to_remove.append(stmt)

        if isinstance(stmt, ast.While):
            remove_useless_assignements([], stmt.body, rhs_expressions)

        if isinstance(stmt, ast.If):
            remove_useless_assignements([], stmt.body, rhs_expressions)
            remove_useless_assignements([], stmt.orelse, rhs_expressions)

    for assignement in assignements_to_remove:
        sentence.remove(assignement)


class CodeFromPEGGenerator(object):

    def __init__(self, peg):

        self.peg = peg
        self.var_counter = 0

    def get_code(self):

        args = self.peg.function_def.args
        name = self.peg.function_def.name

        name_bindings = {}
        for key in self.peg.ctx.keys():
            name_bindings[key] = ast.Name(id=key, ctx=ast.Load())

        ctx = {'retvar': self.peg.ctx['retvar']}

        sentence = self.translate_ctx(ctx, name_bindings)
        basic_block_forward_propagation(sentence, {})
        rhsides = sentence_rhs_expressions(sentence)
        remove_useless_assignements([], sentence, rhsides)

        code = ast.FunctionDef(name=name, args=args, body=sentence, decorator_list=[])
        return code

    def create_fresh_var(self, name='var'):

        self.var_counter += 1
        return name + '_' + str(self.var_counter)

    def fusable(self, fst_node, snd_node):

        assert (isinstance(fst_node, LoopNode) or isinstance(fst_node, BranchNode))
        assert (isinstance(snd_node, LoopNode) or isinstance(snd_node, BranchNode))

        reachable_from_fst = self.peg.nodes_reachable_from(fst_node, [])
        reachable_from_snd = self.peg.nodes_reachable_from(snd_node, [])

        if fst_node in reachable_from_snd or snd_node in reachable_from_fst:
            return False

        return fst_node.condition == snd_node.condition

    def fuse_loops(self, fst_node, snd_node):

        children_keys = []
        children = []

        all_children_keys = fst_node.children_keys + snd_node.children_keys
        all_children = fst_node.children + snd_node.children

        for key, child in zip(all_children_keys, all_children):
            if key not in children_keys:
                children_keys.append(key)
                children.append(child)

        outputs = list(set(fst_node.output_vars + snd_node.output_vars))

        body = fst_node.body
        for key in snd_node.body.keys():
            if key not in body.keys():
                body[key] = snd_node.body[key]

        fst_node.children_keys = children_keys
        fst_node.children = children
        fst_node.body = body
        fst_node.additional_ids.append(snd_node.id)
        fst_node.output_vars = outputs
        assert (fst_node.stmt_ret != None and snd_node.stmt_ret != None)
        fst_node.stmt_ret = fst_node.stmt_ret + snd_node.stmt_ret

        snd_predecessor = snd_node.predecessor
        if snd_predecessor != None:
            snd_predecessor.children.remove(snd_node)

    def fuse_branches(self, fst_node, snd_node):

        children_keys = []
        children = []

        all_children_keys = fst_node.children_keys + snd_node.children_keys
        all_children = fst_node.children + snd_node.children

        for key, child in zip(all_children_keys, all_children):
            if key not in children_keys:
                children_keys.append(key)
                children.append(child)

        outputs = list(set(fst_node.output_vars + snd_node.output_vars))

        true_branch = fst_node.true_branch
        for key in snd_node.true_branch.keys():
            if key not in true_branch.keys():
                true_branch[key] = snd_node.true_branch[key]

        false_branch = fst_node.false_branch
        for key in snd_node.false_branch.keys():
            if key not in false_branch.keys():
                false_branch[key] = snd_node.false_branch[key]

        fst_node.children_keys = children_keys
        fst_node.children = children
        fst_node.true_branch = true_branch
        fst_node.false_branch = false_branch
        fst_node.additional_ids.append(snd_node.id)
        fst_node.output_vars = outputs

        snd_predecessor = snd_node.predecessor
        if snd_predecessor != None:
            snd_predecessor.children.remove(snd_node)

    def compute_loop_invariant_evals(self, ctx):

        loop_invariant_evals = []
        visited = []

        for key in ctx.keys():
            self.compute_loop_invariant_evals_helper(ctx[key], visited, loop_invariant_evals)

        return list(set(loop_invariant_evals))

    def compute_loop_invariant_evals_helper(self, root, visited, loop_invariant_evals):

        if root.id in visited:
            return

        visited.append(root.id)

        if isinstance(root, EvalNode):
            loop_invariant_evals.append(root)
            return

        for child in root.children:
            self.compute_loop_invariant_evals_helper(child, visited, loop_invariant_evals)

    def nodes_reachable_from(self, node):

        visited = []
        reachable_nodes = []

        self.nodes_reachable_from_helper(node, visited, reachable_nodes)

        return reachable_nodes

    def nodes_reachable_from_helper(self, node, visited, reachable_nodes):

        if node.id in visited:
            return

        reachable_nodes.append(node)
        visited.append(node.id)

        for child in node.children:
            self.nodes_reachable_from_helper(child, visited, reachable_nodes)

    def theta_nodes_reachable_from(self, node):

        theta_nodes = []
        visited = []

        for child in node.children:
            self.theta_nodes_reachable_from_helper(child, visited, theta_nodes)

        return theta_nodes

    def theta_nodes_reachable_from_helper(self, node, visited, theta_nodes):

        if node.id in visited or isinstance(node, EvalNode):
            return

        visited.append(node.id)

        if isinstance(node, THETANode):
            theta_nodes.append(node)

        for child in node.children:
            self.theta_nodes_reachable_from_helper(child, visited, theta_nodes)

    def compute_outermost_phi_nodes(self, ctx):

        visited = []
        outermost_phi_nodes = []

        for key in ctx.keys():
            self.compute_outermost_phi_nodes_helper(ctx[key], visited,
                                                    outermost_phi_nodes)

        return outermost_phi_nodes

    def compute_outermost_phi_nodes_helper(self, root, visited, outermost_phi_nodes):

        if root.id in visited:
            return False

        visited.append(root.id)
        has_phi_successors = False

        for child in root.children:

            if self.compute_outermost_phi_nodes_helper(child, visited, outermost_phi_nodes):
                has_phi_successors = True

        if isinstance(root, PHINode) and not has_phi_successors:
            outermost_phi_nodes.append(root)
            return True

        return has_phi_successors

    def nodes_reachable_from_both_phi_branches(self, phi_node):

        assert (isinstance(phi_node, PHINode))

        true_child = phi_node.children[1]
        false_child = phi_node.children[2]

        true_node_children = self.nodes_reachable_from(true_child)
        false_node_children = self.nodes_reachable_from(false_child)

        return list(set(true_node_children) & set(false_node_children))

    def replace_evals_with_loopstmts(self, evals, loopstmts, ctx):

        visited = []

        for key in ctx.keys():

            self.replace_evals_with_loopstmts_helper(evals, loopstmts,
                                                     ctx[key], visited)

            if ctx[key].id in loopstmts:
                eval_id = ctx[key].id
                ctx[key] = loopstmts[eval_id]

    def replace_evals_with_loopstmts_helper(self, evals, loopstmts, root, visited):

        if root.id in visited:
            return

        visited.append(root.id)

        for i in range(len(root.children)):

            self.replace_evals_with_loopstmts_helper(evals, loopstmts,
                                                     root.children[i], visited)

            if root.children[i].id in evals:
                eval_id = root.children[i].id
                loopstmts[eval_id].predecessor = root
                root.children[i] = loopstmts[eval_id]

    def replace_phis_with_branchstmts(self, phis, branchstmts, ctx):

        visited = []

        for key in ctx.keys():

            self.replace_phis_with_branchstmts_helper(phis, branchstmts,
                                                      ctx[key], visited)

            if ctx[key].id in phis:
                phi_id = ctx[key].id
                ctx[key] = branchstmts[phi_id]

    def replace_phis_with_branchstmts_helper(self, phis, branchstmts, root, visited):

        if root.id in visited:
            return

        visited.append(root.id)

        for i in range(len(root.children)):

            self.replace_phis_with_branchstmts_helper(phis, branchstmts,
                                                      root.children[i], visited)

            if root.children[i].id in phis:
                phi_id = root.children[i].id
                branchstmts[phi_id].predecessor = root
                root.children[i] = branchstmts[phi_id]

    def create_modified_copy(self, root, S, vars_map):

        S_ids = [node.id for node in S]

        if root.id in S_ids:
            return Param(root.id, vars_map[root.id])

        copy_root = copy.deepcopy(root)
        visited = []

        self.create_modified_copy_helper(copy_root, visited, S_ids, vars_map)

        return copy_root

    def create_modified_copy_helper(self, node, visited, S_ids, vars_map):

        if node.id in visited:
            return

        visited.append(node.id)

        for i in range(len(node.children)):

            if node.children[i].id in S_ids:
                child_id = node.children[i].id
                var = vars_map[child_id]
                node.children[i] = Param(child_id, var)

            else:
                self.create_modified_copy_helper(node.children[i], visited, S_ids, vars_map)

    def find_fusable_nodes(self, stmt_nodes):

        for i in range(len(stmt_nodes)):
            for j in range(i + 1, len(stmt_nodes)):
                if self.fusable(stmt_nodes[i], stmt_nodes[j]):
                    return (stmt_nodes[i], stmt_nodes[j])

        return None

    def translate_ctx(self, ctx, name_bindings):

        loop_nodes = self.translate_loops(ctx, name_bindings)

        branch_nodes = self.translate_branches(ctx, name_bindings)

        fusable_pair = self.find_fusable_nodes(loop_nodes)
        while fusable_pair != None:
            fst_node, snd_node = fusable_pair
            self.fuse_loops(fst_node, snd_node)
            loop_nodes.remove(snd_node)

            fusable_pair = self.find_fusable_nodes(loop_nodes)

        fusable_pair = self.find_fusable_nodes(branch_nodes)
        while fusable_pair != None:
            fst_node, snd_node = fusable_pair
            self.fuse_branches(fst_node, snd_node)
            branch_nodes.remove(snd_node)

            fusable_pair = self.find_fusable_nodes(branch_nodes)

        final_code = self.sequence(ctx, name_bindings)

        return final_code

    def translate_loops(self, ctx, name_bindings):

        loop_invariant_evals = self.compute_loop_invariant_evals(ctx)
        tagged_theta_nodes = {}

        if len(loop_invariant_evals) == 0:
            return []

        loopstmts = {}

        for li_eval in loop_invariant_evals:

            S = self.theta_nodes_reachable_from(li_eval)
            S = sorted(S, key=lambda theta: theta.loop_depth)
            vars_map = {}

            for node in S:

                assert (isinstance(node, THETANode))
                if not node.id in tagged_theta_nodes.keys():
                    vars_map[node.id] = self.create_fresh_var(node.var_name)
                    tagged_theta_nodes[node.id] = vars_map[node.id]
                else:
                    vars_map[node.id] = tagged_theta_nodes[node.id]

            # extracting loop body
            ctx_iter = {}
            for node in S:
                iter_node = node.children[1]
                modified_iter_node = self.create_modified_copy(iter_node, S, vars_map)

                var = vars_map[node.id]
                ctx_iter[var] = modified_iter_node

            name_bindings_iter = dict.copy(name_bindings)

            # extracting loop break condition
            pass_node = li_eval.children[1]
            cond_node = pass_node.children[0]
            modified_cond_node = self.create_modified_copy(cond_node, S, vars_map)

            cond_var = self.create_fresh_var('cond')
            ctx_cond = {cond_var: modified_cond_node}

            name_bindings_cond = dict.copy(name_bindings)
            stmt_cond = self.translate_ctx(ctx_cond, name_bindings_cond)

            # extracting post loop

            ret_node = li_eval.children[0]

            assert (isinstance(ret_node, THETANode) or isinstance(ret_node, Param) or isinstance(ret_node, NumericNode))
            modified_ret_node = self.create_modified_copy(ret_node, S, vars_map)

            name = ret_node.var_name if isinstance(ret_node, THETANode) else ret_node.name
            ret_var = self.create_fresh_var(name)
            ctx_ret = {ret_var: modified_ret_node}

            name_bindings_ret = dict.copy(name_bindings)
            stmt_ret = self.translate_ctx(ctx_ret, name_bindings_ret)

            break_condition = ast.UnaryOp(op=ast.Not(), operand=ast.Name(id=cond_var, ctx=ast.Load()))

            stmt_node_children_keys = [vars_map[node.id] for node in S]
            stmt_node_children = [node.children[0] for node in S]
            stmt_node_children = list(map(lambda x: Param(x.id, vars_map[x.id]) if x in S else x,
                                          stmt_node_children))

            loop_stmt_node = LoopNode(li_eval.id, stmt_node_children_keys, stmt_node_children,
                                      ctx_iter, [ret_var], cond_node)
            loop_stmt_node.stmt_cond = stmt_cond
            loop_stmt_node.stmt_ret = stmt_ret
            loop_stmt_node.break_condition = break_condition

            loopstmts[loop_stmt_node.id] = loop_stmt_node

        evals = [e.id for e in loop_invariant_evals]
        self.replace_evals_with_loopstmts(evals, loopstmts, ctx)

        return list(loopstmts.values())

    def translate_branches(self, ctx, name_bindings):

        most_nested_phis = self.compute_outermost_phi_nodes(ctx)

        if len(most_nested_phis) == 0:
            return []

        branchstmts = {}


        for mn_phi in most_nested_phis:

            S = self.nodes_reachable_from_both_phi_branches(mn_phi)
            vars_map = {}

            for node in S:
                vars_map[node.id] = self.create_fresh_var()

            fresh_var = self.create_fresh_var()

            true_node = mn_phi.children[1]
            modified_true_node = self.create_modified_copy(true_node, S, vars_map)

            ctx_true = {fresh_var: modified_true_node}
            name_bindings_true = dict.copy(name_bindings)

            false_node = mn_phi.children[2]
            modified_false_node = self.create_modified_copy(false_node, S, vars_map)
            ctx_false = {fresh_var: modified_false_node}
            name_bindings_false = dict.copy(name_bindings)

            cond_node = mn_phi.children[0]
            modified_cond_node = self.create_modified_copy(cond_node, S, vars_map)
            cond_var = self.create_fresh_var('cond')
            ctx_cond = {cond_var: modified_cond_node}
            name_bindings_cond = dict.copy(name_bindings)
            stmt_cond = self.translate_ctx(ctx_cond, name_bindings_cond)

            stmt_node_children_keys = [vars_map[node.id] for node in S]
            stmt_node_children = [node for node in S]

            branch_stmt_node = BranchNode(mn_phi.id, stmt_node_children_keys, stmt_node_children,
                                          ctx_true, ctx_false, [fresh_var], cond_node)

            branch_stmt_node.stmt_cond = stmt_cond
            branch_stmt_node.predicate = cond_var

            branchstmts[branch_stmt_node.id] = branch_stmt_node

        phis = [ph.id for ph in most_nested_phis]
        self.replace_phis_with_branchstmts(phis, branchstmts, ctx)

        return list(branchstmts.values()) + self.translate_branches(ctx, name_bindings)

    def sequence(self, ctx, name_bindings):

        tmp_node = TemporaryNode(_id=0, name='tmp')

        sorted_keys = list(ctx.keys())
        sorted_keys = sorted(sorted_keys)

        sentence = []

        for key in sorted_keys:
            tmp_node.children.append(ctx[key])

        self.sequence_helper(tmp_node, sentence, name_bindings)

        for updated_child, key in zip(tmp_node.children, sorted_keys):
            ctx[key] = updated_child

            target = ast.Name(id=key, ctx=ast.Store())

            if isinstance(ctx[key], Param):

                value = ast.Name(id=ctx[key].name, ctx=ast.Load())

            elif isinstance(ctx[key], NumericNode):

                value = ctx[key].value

            else:
                print('strange', ctx[key])

            if key == 'retvar':
                sentence.append(ast.Return(value=value))
            else:
                sentence.append(ast.Assign(targets=[target], value=value))

        return sentence

    def sequence_helper(self, root, sentence, name_bindings):

        for i in range(len(root.children)):
            self.sequence_helper(root.children[i], sentence, name_bindings)

            if isinstance(root.children[i], LoopNode):

                loop_node = root.children[i]

                for key, val in zip(loop_node.children_keys, loop_node.children):

                    target = ast.Name(id=key, ctx=ast.Store())

                    assert (isinstance(val, Param) or isinstance(val, NumericNode))
                    if isinstance(val, NumericNode):
                        value = val.token
                    else:
                        value = ast.Name(id=val.name, ctx=ast.Load())
                    init_assignement = ast.Assign(targets=[target], value=value)
                    name_bindings[target] = value
                    sentence.append(init_assignement)

                iter_stmt = self.translate_ctx(loop_node.body, name_bindings)
                loop_node_stmt = loop_node.compute_stmt(iter_stmt)

                for each in loop_node_stmt:
                    sentence.append(each)

                root.children[i] = Param(loop_node.id, loop_node.output_vars[0])

                if len(loop_node.output_vars) > 1:
                    for var, _id in zip(loop_node.output_vars[1:], loop_node.additional_ids):
                        root.children.append(Param(_id, var))
                    print(root, list(map(lambda x: x.name, root.children)))

            if isinstance(root.children[i], BranchNode):

                branch_node = root.children[i]

                for key, val in zip(branch_node.children_keys, branch_node.children):

                    target = ast.Name(id=key, ctx=ast.Store())

                    assert (isinstance(val, Param) or isinstance(val, NumericNode))
                    if isinstance(val, NumericNode):
                        value = val.token
                    else:
                        value = ast.Name(id=val.name, ctx=ast.Load())

                    init_assignement = ast.Assign(targets=[target], value=value)
                    name_bindings[target] = value
                    sentence.append(init_assignement)

                true_stmt = self.translate_ctx(branch_node.true_branch, name_bindings)
                false_stmt = self.translate_ctx(branch_node.false_branch, name_bindings)
                branch_node_stmt = branch_node.compute_stmt(true_stmt, false_stmt)

                for each in branch_node_stmt:
                    sentence.append(each)

                root.children[i] = Param(branch_node.id, branch_node.output_vars[0])

                if len(branch_node.output_vars) > 1:
                    for var, _id in zip(branch_node.output_vars[1:], branch_node.additional_ids):
                        root.children.append(Param(_id, var))

            if isinstance(root.children[i], BinOpNode):

                operator = root.children[i]

                for arg in operator.children:
                    assert (isinstance(arg, Param) or isinstance(arg, NumericNode))

                fresh_var = self.create_fresh_var('op')
                target = ast.Name(id=fresh_var, ctx=ast.Store())
                args = [ast.Name(id=param.name, ctx=ast.Load())
                        if isinstance(param, Param)
                        else param.token
                        for param in operator.children]
                op_expr = ast.BinOp(left=args[0], op=operator.op, right=args[1])
                op_assignement = ast.Assign(targets=[target], value=op_expr)
                name_bindings[target] = op_expr

                sentence.append(op_assignement)
                root.children[i] = Param(operator.id, fresh_var)

            if isinstance(root.children[i], FunctionCall):

                func_call = root.children[i]

                for arg in func_call.children:
                    assert (isinstance(arg, Param) or isinstance(arg, NumericNode))

                fresh_var = self.create_fresh_var(func_call.name)
                target = ast.Name(id=fresh_var, ctx=ast.Store())
                args = [ast.Name(id=param.name, ctx=ast.Load())
                        if isinstance(param, Param)
                        else param.token
                        for param in func_call.children]

                func_call_expr = ast.Call(func=ast.Name(id=func_call.name, ctx=ast.Load()), args=args, keywords=[])
                func_assignement = ast.Assign(targets=[target], value=func_call_expr)

                sentence.append(func_assignement)
                root.children[i] = Param(func_call.id, fresh_var)

            if isinstance(root.children[i], CompareNode):

                compare = root.children[i]

                assert (isinstance(compare.head(), Param) or isinstance(compare.head(), NumericNode))

                for arg in compare.tail():
                    assert (isinstance(arg, Param) or isinstance(arg, NumericNode))

                fresh_var = self.create_fresh_var('comp')
                target = ast.Name(id=fresh_var, ctx=ast.Store())
                if isinstance(compare.head(), Param):
                    head = ast.Name(id=compare.head().name, ctx=ast.Load())
                else:
                    head = compare.head().token
                tail = [ast.Name(id=param.name, ctx=ast.Load()) if isinstance(param, Param) else param.token
                        for param in compare.tail()]
                cmp_expr = ast.Compare(left=head, ops=compare.ops, comparators=tail)
                cmp_assignement = ast.Assign(targets=[target], value=cmp_expr)
                name_bindings[target] = cmp_expr

                sentence.append(cmp_assignement)
                root.children[i] = Param(compare.id, fresh_var)

            if isinstance(root.children[i], UnaryOpNode):

                unop_node = root.children[i]

                assert (isinstance(unop_node.operand(), Param) or isinstance(unop_node.operand(), NumericNode))
                fresh_var = self.create_fresh_var('unary_op_expr')
                target = ast.Name(id=fresh_var, ctx=ast.Store())
                if isinstance(unop_node.operand(), Param):
                    operand = ast.Name(id=unop_node.operand().name, ctx=ast.Load())
                else:
                    operand = unop_node.operand().token

                unop_expr = ast.UnaryOp(op=unop_node.op,
                                        operand=operand)
                unop_assignement = ast.Assign(targets=[target], value=unop_expr)
                name_bindings[target] = unop_expr
                sentence.append(unop_assignement)
                root.children[i] = Param(unop_node.id, fresh_var)

            if isinstance(root.children[i], NumericNode):
                pass

            if isinstance(root.children[i], Param):
                pass




