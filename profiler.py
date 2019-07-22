import ast, astor
from optimize_function import is_optimizable
import subprocess
import re


def is_leaf_node(node):

    return isinstance(node, ast.Name) or isinstance(node, ast.Num) or isinstance(node, ast.Str)


def is_stmt_to_visit(node):

    return isinstance(node, ast.While) or isinstance(node, ast.For) or isinstance(node, ast.If) or \
           isinstance(node, ast.Assign) or isinstance(node, ast.FunctionDef) or isinstance(node, ast.Return) or \
            isinstance(node, ast.AugAssign)


class TACGenerator(ast.NodeTransformer):

    def __init__(self):

        self.counter = 0
        self.current_block_code = []


    def compute_fresh_var(self):

        self.counter += 1
        return 'var_' + str(self.counter)


    def visit_ListComp(self, node):

        return node

    def visit_Module(self, node):

        self.current_block_code = []

        for stmt in node.body:
            if is_stmt_to_visit(stmt):
                self.visit(stmt)
            else:
                self.current_block_code.append(stmt)

        body = self.current_block_code
        return ast.Module(body=body)

    def visit_FunctionDef(self, node):

        if not is_optimizable(node):

            self.current_block_code.append(node)
            return node

        outer_code = self.current_block_code
        self.current_block_code = []

        for stmt in node.body:
            if is_stmt_to_visit(stmt):
                self.visit(stmt)
            else:
                self.current_block_code.append(stmt)

        body = self.current_block_code
        self.current_block_code = outer_code

        decorator_list = [n for n in node.decorator_list if not (isinstance(n, ast.Name) and n.id=='opt')]
        if len([n.id for n in decorator_list if isinstance(n, ast.Name) and n.id == 'profile']) == 0:
            decorator_list += [ast.Name(id='profile', ctx=ast.Load())]

        new_node = ast.FunctionDef(name=node.name, args=node.args, body=body, decorator_list=decorator_list,
                               returns=node.returns)

        self.current_block_code.append(new_node)

        return new_node

    def visit_Assign(self, node):

        value = self.visit(node.value)
        new_node = ast.Assign(targets=node.targets, value=value)
        self.current_block_code.append(new_node)

        return new_node


    def visit_AugAssign(self, node):

        var = node.target
        operator = ast.BinOp(left=var, op=node.op, right=node.value)
        updated_operator = self.visit(operator)

        new_node = ast.Assign(targets=[var], value=updated_operator)
        self.current_block_code.append(new_node)

        return new_node

    def visit_Return(self, node):

        value = self.visit(node.value)
        new_node = ast.Return(value=value)
        self.current_block_code.append(new_node)

        return new_node


    def visit_Call(self, node):

        args = [self.visit(a) for a in node.args]
        fresh_var = self.compute_fresh_var()

        target = ast.Name(id=fresh_var, ctx=ast.Store())
        assignement = ast.Assign(targets=[target], value=node)
        self.current_block_code.append(assignement)
        node.args = args

        return target

    def visit_Attribute(self, node):

        val = self.visit(node.value)
        fresh_var = self.compute_fresh_var()

        target = ast.Name(id=fresh_var, ctx=ast.Store())
        assignement = ast.Assign(targets=[target], value=val)
        self.current_block_code.append(assignement)
        node.value = val

        return target

    def visit_BinOp(self, node):

        left_node = self.visit(node.left)
        right_node = self.visit(node.right)
        fresh_var = self.compute_fresh_var()

        node.left = left_node
        node.right = right_node

        target = ast.Name(id=fresh_var, ctx=ast.Store())
        assignement = ast.Assign(targets=[target], value=node)
        self.current_block_code.append(assignement)

        return target

    def visit_If(self, node):

        test_node = self.visit(node.test)
        outer_code = self.current_block_code
        self.current_block_code = []

        for stmt in node.body:
            if is_stmt_to_visit(stmt):
                self.visit(stmt)
            else:
                self.current_block_code.append(stmt)

        body = self.current_block_code
        self.current_block_code = []

        for stmt in node.orelse:
            if is_stmt_to_visit(stmt):
                self.visit(stmt)
            else:
                self.current_block_code.append(stmt)

        orelse = self.current_block_code
        self.current_block_code = outer_code

        new_node = ast.If(test=test_node, body=body, orelse=orelse)
        self.current_block_code.append(new_node)

        return new_node

    def visit_While(self, node):

        test_node = node.test
        outer_code = self.current_block_code
        self.current_block_code = []

        for stmt in node.body:
            if is_stmt_to_visit(stmt):
                self.visit(stmt)
            else:
                self.current_block_code.append(stmt)

        body = self.current_block_code
        self.current_block_code = []

        for stmt in node.orelse:
            if is_stmt_to_visit(stmt):
                self.visit(stmt)
            else:
                self.current_block_code.append(stmt)

        orelse = self.current_block_code
        self.current_block_code = outer_code

        new_node = ast.While(test=test_node, body=body, orelse=orelse)
        self.current_block_code.append(new_node)

        return new_node

    def visit_For(self, node):

        outer_code = self.current_block_code
        self.current_block_code = []

        for stmt in node.body:
            if is_stmt_to_visit(stmt):
                self.visit(stmt)
            else:
                self.current_block_code.append(stmt)

        body = self.current_block_code
        self.current_block_code = []

        for stmt in node.orelse:
            if is_stmt_to_visit(stmt):
                self.visit(stmt)
            else:
                self.current_block_code.append(stmt)

        orelse = self.current_block_code
        self.current_block_code = outer_code

        node.body = body
        node.orelse = orelse

        self.current_block_code.append(node)

        return node


def generate_tac_code(tree_init):

    tree = TACGenerator().visit(tree_init)

    f = open('tac.py', 'w')
    f.write(astor.to_source(tree))


def profile(args=[]):

    subprocess.call(['kernprof', '-l', 'tac.py'] + args)

    profiler_output = subprocess.check_output(['python3', '-m', 'line_profiler', 'tac.py.lprof']).decode("utf-8")
    line_durations = {}
    line_pattern = re.compile("((\d+\.?\d*)\s+){5}")

    for line in profiler_output.splitlines():

        if line_pattern.search(line) != None:
            lineno = int(line.split()[0])
            duration = int(float(line.split()[2]))
            line_durations[lineno] = duration

    return line_durations

