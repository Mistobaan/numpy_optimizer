from peg_nodes import PEGNode, BinOpNode, CompareNode, BytesNode, NumericNode, ListNode
from peg_nodes import LeafNode, StringNode, DictNode, TupleNode, UnaryOpNode, SetNode, FunctionCall, BoolOpNode
from peg_nodes import THETANode, PHINode, EvalNode, PassNode, Param, TemporaryNode
from peg_nodes import AttributeNode, SubscriptNode, SliceNode, ExtSliceNode, IndexNode
import copy
import ast
import astor


def replace_node(old_node, new_node):

    for pred in old_node.predecessors:

        indices = [i for i in range(len(pred.children)) if pred.children[i].id == old_node.id]

        for i in indices:
            pred.children[i] = new_node

        new_node.predecessors.append(pred)

    if old_node in new_node.predecessors:
        new_node.predecessors.remove(old_node)


def reset_predecessors(root, visited):

    if root.id in visited:
        return

    visited.append(root.id)
    root.predecessors = []

    for child in root.children:
        reset_predecessors(child, visited)


def compute_predecessors(root):

    visited = []
    reset_predecessors(root, visited)
    visited = []

    compute_predecessors_helper(root, visited)


def compute_predecessors_helper(root, visited):
    if root.id in visited:
        return

    visited.append(root.id)

    for child in root.children:
        child.predecessors.append(root)
        compute_predecessors_helper(child, visited)



class StmtNode(PEGNode):

    def __init__(self, _id, children_keys, children, stmt, output_var):
        self.id = _id
        self.children_keys = children_keys
        self.children = children
        self.stmt = stmt
        self.output_var = output_var



class StmtLoopBodyCtx():

    def __init__(self, body):
        self.body = body
        self.computed = False

class StmtBranchesCtx():

    def __init__(self, true_branch, false_branch):
        self.true_branch = true_branch
        self.false_branch = false_branch
        self.computed = False


def merge_dicts(d1, d2):

    result = d1

    for key in d2.keys():
        if key not in result.keys():
            result[key] = d2[key]


    return result


class LoopNode(PEGNode):

    def __init__(self, _id, children_keys, children, body_ctx, output_var, condition):
        self.id = _id
        self.children_keys = children_keys
        self.children = children
        self.body_ctx = body_ctx
        self.output_var = output_var
        self.condition = condition
        self.additional_ids = []
        self.stmt = None
        self.predecessors = []
        self.stmt_ret = None
        self.stmt_cond = None
        self.break_condition = None

    def compute_stmt(self, stmt_iter):

        loop_stmt = self.stmt_cond + [ast.While(test=self.break_condition,
                                                body=(stmt_iter + self.stmt_cond), orelse=[])] + self.stmt_ret

        return loop_stmt


class BranchNode(PEGNode):

    def __init__(self, _id, children_keys, children, body_ctx, output_var, condition):
        self.id = _id
        self.children_keys = children_keys
        self.children = children
        self.body_ctx = body_ctx
        self.output_var = output_var
        self.condition = condition
        self.additional_ids = []
        self.true_stmt = None
        self.false_stmt = None
        self.predecessors = []
        self.stmt_cond = None
        self.predicate = None

    def compute_stmt(self, true_stmt, false_stmt):

        branch_stmt = self.stmt_cond + [ast.If(test=ast.Name(id=self.predicate, ctx=ast.Load()),
                                               body=true_stmt, orelse=false_stmt)]

        return branch_stmt




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

        name_bindings = {}
        #basic_block_forward_propagation(sentence, name_bindings)

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

        return fst_node.condition.id == snd_node.condition.id

    def fuse_loops(self, fst_node, snd_node):


        merged_body = merge_dicts(fst_node.body_ctx.body, snd_node.body_ctx.body)

        merged_children_keys = fst_node.children_keys
        merged_children = fst_node.children

        for key, value in zip(snd_node.children_keys, snd_node.children):
            if not key in merged_children_keys:
                merged_children_keys.append(key)
                merged_children.append(value)

        fst_node.body_ctx.body = merged_body
        snd_node.body_ctx = fst_node.body_ctx
        fst_node.children_keys = merged_children_keys
        snd_node.children_keys = merged_children_keys
        fst_node.children = merged_children
        snd_node.children = merged_children
        assert (fst_node.stmt_ret != None and snd_node.stmt_ret != None)
        fst_node.stmt_ret = fst_node.stmt_ret + snd_node.stmt_ret


    def fuse_branches(self, fst_node, snd_node):


        merged_true_branch = merge_dicts(fst_node.body_ctx.true_branch, snd_node.body_ctx.true_branch)
        merged_false_branch = merge_dicts(fst_node.body_ctx.false_branch, snd_node.body_ctx.false_branch)
        merged_children_keys = fst_node.children_keys
        merged_children = fst_node.children

        for key, value in zip(snd_node.children_keys, snd_node.children):
            if not key in merged_children_keys:
                merged_children_keys.append(key)
                merged_children.append(value)

        fst_node.body_ctx.true_branch = merged_true_branch
        snd_node.body_ctx.false_branch = merged_false_branch
        fst_node.children_keys = merged_children_keys
        snd_node.children_keys = merged_children_keys
        fst_node.children = merged_children
        snd_node.children = merged_children

        snd_node.body_ctx = fst_node.body_ctx


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

        assert(isinstance(node, EvalNode))
        current_depth = node.loop_depth

        for child in node.children:
            self.theta_nodes_reachable_from_helper(child, visited, theta_nodes, current_depth)

        return theta_nodes

    def theta_nodes_reachable_from_helper(self, node, visited, theta_nodes, current_depth):

        if node.id in visited or (isinstance(node, EvalNode) and node.loop_depth == current_depth):
            return

        visited.append(node.id)

        if isinstance(node, THETANode) and node.loop_depth == current_depth:
            theta_nodes.append(node)

        for child in node.children:
            self.theta_nodes_reachable_from_helper(child, visited, theta_nodes, current_depth)

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
                eval_node = root.children[i]

                replace_node(eval_node, loopstmts[eval_node.id])
                evals.remove(eval_node.id)


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
                phi_node = root.children[i]
                replace_node(phi_node, branchstmts[phi_node.id])




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

        tagged_theta_nodes = {}
        loop_nodes = self.translate_loops(ctx, name_bindings, tagged_theta_nodes)


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

    def translate_loops(self, ctx, name_bindings, tagged_theta_nodes):

        loop_invariant_evals = self.compute_loop_invariant_evals(ctx)

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

            assert (isinstance(ret_node, THETANode) or isinstance(ret_node, LeafNode))
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

            loop_body_cxt = StmtLoopBodyCtx(ctx_iter)
            loop_stmt_node = LoopNode(li_eval.id, stmt_node_children_keys, stmt_node_children,
                                      loop_body_cxt, ret_var, cond_node)
            loop_stmt_node.stmt_cond = stmt_cond
            loop_stmt_node.stmt_ret = stmt_ret
            loop_stmt_node.break_condition = break_condition

            loopstmts[loop_stmt_node.id] = loop_stmt_node

        evals = [e.id for e in loop_invariant_evals]
        self.replace_evals_with_loopstmts(evals, loopstmts, ctx)

        lstmts = [lstmt for lstmt in loopstmts.values() if isinstance(lstmt, LoopNode)]

        return lstmts + self.translate_loops(ctx, name_bindings, tagged_theta_nodes)


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

            false_node = mn_phi.children[2]
            modified_false_node = self.create_modified_copy(false_node, S, vars_map)
            ctx_false = {fresh_var: modified_false_node}

            cond_node = mn_phi.children[0]
            modified_cond_node = self.create_modified_copy(cond_node, S, vars_map)
            cond_var = self.create_fresh_var('cond')
            ctx_cond = {cond_var: modified_cond_node}
            name_bindings_cond = dict.copy(name_bindings)
            stmt_cond = self.translate_ctx(ctx_cond, name_bindings_cond)

            stmt_node_children_keys = [vars_map[node.id] for node in S]
            stmt_node_children = [node for node in S]

            branch_body_ctx = StmtBranchesCtx(ctx_true, ctx_false)
            branch_stmt_node = BranchNode(mn_phi.id, stmt_node_children_keys, stmt_node_children,
                                          branch_body_ctx, fresh_var, cond_node)

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

        compute_predecessors(tmp_node)

        self.sequence_helper(tmp_node, sentence, name_bindings)

        for updated_child, key in zip(tmp_node.children, sorted_keys):
            ctx[key] = updated_child

            target = ast.Name(id=key, ctx=ast.Store())
            if isinstance(ctx[key], LoopNode) or isinstance(ctx[key], BranchNode):
                value = ast.Name(id=ctx[key].output_var, ctx=ast.Load())
                # extract body
            else:
                assert(isinstance(ctx[key], LeafNode))
                value = ctx[key].token

            if key == 'retvar':
                sentence.append(ast.Return(value=value))
            else:
                sentence.append(ast.Assign(targets=[target], value=value))

        return sentence

    def sequence_helper(self, root, sentence, name_bindings):


        for i in range(len(root.children)):

            self.sequence_helper(root.children[i], sentence, name_bindings)


            for child in root.children[i].children:
                assert(isinstance(child, LeafNode))

            if isinstance(root.children[i], LoopNode):

                loop_node = root.children[i]

                if not loop_node.body_ctx.computed:

                    for key, val in zip(loop_node.children_keys, loop_node.children):
                        target = ast.Name(id=key, ctx=ast.Store())
                        value = val.token

                        init_assignement = ast.Assign(targets=[target], value=value)
                        name_bindings[target] = value
                        sentence.append(init_assignement)

                    iter_stmt = self.translate_ctx(loop_node.body_ctx.body, name_bindings)
                    loop_node_stmt = loop_node.compute_stmt(iter_stmt)
                    loop_node.body_ctx.computed = True

                    for stmt in loop_node_stmt:
                        sentence.append(stmt)

                param_node = Param(loop_node.id, loop_node.output_var)

                replace_node(loop_node, param_node)


            if isinstance(root.children[i], BranchNode):

                branch_node = root.children[i]

                if not branch_node.body_ctx.computed:

                    for key, val in zip(branch_node.children_keys, branch_node.children):
                        target = ast.Name(id=key, ctx=ast.Store())
                        value = val.token

                        init_assignement = ast.Assign(targets=[target], value=value)
                        name_bindings[target] = value
                        sentence.append(init_assignement)

                    true_stmt = self.translate_ctx(branch_node.body_ctx.true_branch, name_bindings)
                    false_stmt = self.translate_ctx(branch_node.body_ctx.false_branch, name_bindings)
                    branch_node_stmt = branch_node.compute_stmt(true_stmt, false_stmt)
                    branch_node.body_ctx.computed = True

                    for stmt in branch_node_stmt:
                        sentence.append(stmt)

                param_node = Param(branch_node.id, branch_node.output_var)

                replace_node(branch_node, param_node)


            if isinstance(root.children[i], BinOpNode):

                operator = root.children[i]

                fresh_var = self.create_fresh_var('op')
                target = ast.Name(id=fresh_var, ctx=ast.Store())
                args = [arg.token for arg in operator.children]
                op_exp = ast.BinOp(left=args[0], op=operator.op, right=args[1])
                op_assignement = ast.Assign(targets=[target], value=op_exp)
                name_bindings[target] = op_exp

                sentence.append(op_assignement)

                param_node = Param(operator.id, fresh_var)
                replace_node(operator, param_node)


            if isinstance(root.children[i], FunctionCall):

                func_call = root.children[i]

                fresh_var = self.create_fresh_var('func_call')
                target = ast.Name(id=fresh_var, ctx=ast.Store())

                name = func_call.name().token
                args = [arg.token for arg in func_call.args()]

                func_call_exp = ast.Call(func=name, args=args, keywords=[])
                func_assignement = ast.Assign(targets=[target], value=func_call_exp)

                sentence.append(func_assignement)
                param_node = Param(func_call.id, fresh_var)

                replace_node(func_call, param_node)


            if isinstance(root.children[i], CompareNode):

                compare = root.children[i]

                fresh_var = self.create_fresh_var('comp')
                target = ast.Name(id=fresh_var, ctx=ast.Store())
                head = compare.head().token
                tail = [arg.token for arg in compare.tail()]

                cmp_exp = ast.Compare(left=head, ops=compare.ops, comparators=tail)
                cmp_assignement = ast.Assign(targets=[target], value=cmp_exp)
                name_bindings[target] = cmp_exp

                sentence.append(cmp_assignement)
                param_node = Param(compare.id, fresh_var)

                replace_node(compare, param_node)


            if isinstance(root.children[i], BoolOpNode):

                bool_op_node = root.children[i]

                fresh_var = self.create_fresh_var('bool_op')
                target = ast.Name(id=fresh_var, ctx=ast.Store())
                values = [arg.token for arg in bool_op_node.children]

                bool_op_exp = ast.BoolOp(op=bool_op_node.op, values=values)
                bool_op_assignement = ast.Assign(targets=[target], value=bool_op_exp)
                name_bindings[target] = bool_op_exp

                sentence.append(bool_op_assignement)

                param_node = Param(bool_op_node.id, fresh_var)
                replace_node(bool_op_node, param_node)


            if isinstance(root.children[i], UnaryOpNode):

                un_op_node = root.children[i]

                fresh_var = self.create_fresh_var('unary_op_exp')
                target = ast.Name(id=fresh_var, ctx=ast.Store())
                operand = un_op_node.operand().token

                un_op_exp = ast.UnaryOp(op=un_op_node.op, operand=operand)
                un_op_assignement = ast.Assign(targets=[target], value=un_op_exp)
                name_bindings[target] = un_op_exp

                sentence.append(un_op_assignement)
                param_node = Param(un_op_node.id, fresh_var)
                replace_node(un_op_node, param_node)


            if isinstance(root.children[i], ListNode):

                list_node = root.children[i]

                fresh_var = self.create_fresh_var('list_exp')
                target = ast.Name(id=fresh_var, ctx=ast.Store())
                elts = [elem.token for elem in list_node.children]

                list_exp = ast.List(elts=elts, ctx=ast.Load())
                list_assignement = ast.Assign(targets=[target], value=list_exp)
                name_bindings[target] = list_exp

                sentence.append(list_assignement)
                param_node = Param(list_node.id, fresh_var)

                replace_node(list_node, param_node)


            if isinstance(root.children[i], TupleNode):

                tuple_node = root.children[i]

                fresh_var = self.create_fresh_var('tuple_exp')
                target = ast.Name(id=fresh_var, ctx=ast.Store())
                elts = [elem.token for elem in tuple_node.children]

                tuple_exp = ast.Tuple(elts=elts, ctx=ast.Load())
                tuple_assignement = ast.Assign(targets=[target], value=tuple_exp)
                name_bindings[target] = tuple_exp

                sentence.append(tuple_assignement)
                param_node = Param(tuple_node.id, fresh_var)

                replace_node(tuple_node, param_node)


            if isinstance(root.children[i], SetNode):

                set_node = root.children[i]

                fresh_var = self.create_fresh_var('set_exp')
                target = ast.Name(id=fresh_var, ctx=ast.Store())
                elts = [elem.token for elem in set_node.children]

                set_exp = ast.Set(elts=elts, ctx=ast.Load())
                set_assignement = ast.Assign(targets=[target], value=set_exp)
                name_bindings[target] = set_exp

                sentence.append(set_assignement)
                param_node = Param(set_node.id, fresh_var)

                replace_node(set_node, param_node)


            if isinstance(root.children[i], DictNode):

                dict_node = root.children[i]

                fresh_var = self.create_fresh_var('dict_exp')
                target = ast.Name(id=fresh_var, ctx=ast.Store())

                keys = [k.token for k in dict_node.keys()]
                values = [v.token for v in dict_node.values()]

                dict_exp = ast.Dict(keys=keys, values=values, ctx=ast.Load())
                dict_assignement = ast.Assign(targets=[target], value=dict_exp)
                name_bindings[target] = dict_exp

                sentence.append(dict_assignement)
                param_node = Param(dict_node.id, fresh_var)

                replace_node(dict_node, param_node)

            if isinstance(root.children[i], AttributeNode):

                attr_node = root.children[i]

                fresh_var = self.create_fresh_var('attr_exp')
                target = ast.Name(id=fresh_var, ctx=ast.Store())

                value = attr_node.value().token
                attr = attr_node.attr

                attr_exp = ast.Attribute(value=value, attr=attr, ctx=ast.Load())
                attr_assignement = ast.Assign(targets=[target], value=attr_exp)
                name_bindings[target] = attr_exp

                sentence.append(attr_assignement)
                param_node = Param(attr_node.id, fresh_var)

                replace_node(attr_node, param_node)

            if isinstance(root.children[i], SubscriptNode):
                subs_node = root.children[i]

                fresh_var = self.create_fresh_var('subs_exp')
                target = ast.Name(id=fresh_var, ctx=ast.Store())

                value = subs_node.value().token
                slice = subs_node.slice().token

                subs_exp = ast.Subscript(value=value, slice=slice, ctx=ast.Load())
                subs_assignement = ast.Assign(targets=[target], value=subs_exp)
                name_bindings[target] = subs_exp

                sentence.append(subs_assignement)
                param_node = Param(subs_node.id, fresh_var)

                replace_node(subs_node, param_node)

            if isinstance(root.children[i], IndexNode):
                idx_node = root.children[i]

                fresh_var = self.create_fresh_var('idx_exp')
                target = ast.Name(id=fresh_var, ctx=ast.Store())

                value = idx_node.value().token

                idx_exp = ast.Index(value=value)
                idx_assignement = ast.Assign(targets=[target], value=idx_exp)
                name_bindings[target] = idx_exp

                sentence.append(idx_assignement)
                param_node = Param(idx_node.id, fresh_var)

                replace_node(idx_node, param_node)

            if isinstance(root.children[i], SliceNode):
                slice_node = root.children[i]

                fresh_var = self.create_fresh_var('slice_exp')
                target = ast.Name(id=fresh_var, ctx=ast.Store())

                lower = slice_node.lower().token
                upper = slice_node.upper().token
                step = slice_node.step().token

                slice_exp = ast.Slice(lower=lower, upper=upper, step=step)
                slice_assignement = ast.Assign(targets=[target], value=slice_exp)
                name_bindings[target] = slice_exp

                sentence.append(slice_assignement)
                param_node = Param(slice_node.id, fresh_var)

                replace_node(slice_node, param_node)

            if isinstance(root.children[i], ExtSliceNode):
                eslice_node = root.children[i]

                fresh_var = self.create_fresh_var('eslice_exp')
                target = ast.Name(id=fresh_var, ctx=ast.Store())

                dims = [d.token for d in eslice_node.dims()]

                eslice_exp = ast.ExtSlice(dims=dims)
                eslice_assignement = ast.Assign(targets=[target], value=eslice_exp)
                name_bindings[target] = eslice_exp

                sentence.append(eslice_assignement)
                param_node = Param(eslice_node.id, fresh_var)

                replace_node(eslice_node, param_node)



