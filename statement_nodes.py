from peg_nodes import PEGNode
import ast
from ast_utils import is_forloop_iter_stmt


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

    def compute_forloop_stmt(self, stmt_iter, loop_var, iter_obj):

        unused_vars = []
        body = []

        for stmt in stmt_iter:
            if is_forloop_iter_stmt(stmt, loop_var):
                unused_vars.append(stmt.targets[0].id)
            elif isinstance(stmt, ast.Assign) and isinstance(stmt.value, ast.Name) and stmt.value.id in unused_vars:
                unused_vars.append(stmt.targets[0])
            else:
                body.append(stmt)

        loop_stmt = [ast.For(target=loop_var, iter=iter_obj, body=body, orelse=[])] + self.stmt_ret

        return loop_stmt

    def compute_whileloop_stmt(self, stmt_iter):

        if len(self.stmt_cond) == 1:

            assert(isinstance(self.stmt_cond[0], ast.Assign) and isinstance(self.stmt_cond[0].value, ast.UnaryOp))

            negated_break_condition = self.stmt_cond[0].value

            assert(isinstance(negated_break_condition.op, ast.Not))

            break_condition = negated_break_condition.operand
            loop_stmt = [ast.While(test=break_condition,
                                                    body=stmt_iter, orelse=[])] + self.stmt_ret

        else:
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

        if len(self.stmt_cond) == 1:
            assert(isinstance(self.stmt_cond[0], ast.Assign))

            test = self.stmt_cond[0].value
            branch_stmt = [ast.If(test=test, body=true_stmt, orelse=false_stmt)]

        else:
            branch_stmt = self.stmt_cond + [ast.If(test=ast.Name(id=self.predicate, ctx=ast.Load()),
                                               body=true_stmt, orelse=false_stmt)]

        return branch_stmt



