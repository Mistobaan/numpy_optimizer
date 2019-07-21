import ast

def is_forloop_initializer(stmt):

    return isinstance(stmt, ast.Assign) and isinstance(stmt.value, ast.Call) and \
            isinstance(stmt.value.func, ast.Name) and stmt.value.func.id == 'next' and \
           isinstance(stmt.value.args[0], ast.Call) and isinstance(stmt.value.args[0].func, ast.Name) and \
            stmt.value.args[0].func.id == 'iter'


def get_forloop_var(stmt):

    assert(is_forloop_initializer(stmt))

    name = stmt.targets[0]
    assert isinstance(name, ast.Name)

    return name


def get_forloop_iter_obj(stmt):

    assert (is_forloop_initializer(stmt))

    return stmt.value.args[0].args[0]


def is_forloop_iter_stmt(stmt, var):

    return isinstance(stmt, ast.Assign) and isinstance(stmt.value, ast.Call) and \
        isinstance(stmt.value.func, ast.Name) and stmt.value.func.id == 'next' and \
        isinstance(stmt.value.args[0], ast.Name) and stmt.value.args[0].id == var.id


def create_ast_var(id, ctx):

    return ast.Name(id=id, ctx=ctx);


def create_original_and_tmp_assignements(var, expression):

    target = create_ast_var(id=var, ctx=ast.Store())
    tmp_var = create_ast_var(id=var + '_tmp', ctx=ast.Store())
    original = ast.Assign(targets=[target], value=expression)
    tmp = ast.Assign(targets=[tmp_var], value=target)

    return original, tmp