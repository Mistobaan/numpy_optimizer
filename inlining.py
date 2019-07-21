import ast, astor
import copy


def ax_format_to_funcdef(ax_src):

    tree = ast.parse(ax_src)

    args = ast.arguments(args=[], vararg=None, kwonlyargs=[], kw_defaults=[], kwarg=None, defaults=[])
    tree.body.append(ast.Return(value=ast.NameConstant(None)))
    func_def = ast.FunctionDef(name='f', body=tree.body, args=args, decorator_list=[])

    return astor.to_source(func_def)


class InlineSubstitution(ast.NodeTransformer):

    def __init__(self, var_name):
        self.var_name = var_name

    def visit_Name(self, node):

        if node.id == self.var_name:
            node.id = '_' + self.var_name

        return node


def inline_axiom(function_def):

    function_args = [each.arg for each in function_def.args.args]
    function_name = function_def.name

    inline_function_def = copy.deepcopy(function_def)

    for arg in function_args:

        inline_function_def = InlineSubstitution(arg).visit(inline_function_def)


    ann_assigns = []
    fresh_vars_assigns = []
    for arg in function_args:
        ann_assigns.append(ast.AnnAssign(target=ast.Name(id='_'+arg, ctx=ast.Store()), value=None,
                                         annotation=ast.Name(id='PEGNode', ctx=ast.Load()), simple=1))

        fresh_vars_assigns.append(ast.Assign(targets=[ast.Name(id='_'+arg+'_fresh', ctx=ast.Store())],
                           value=ast.Name(id='_'+arg, ctx=ast.Load())))


    function_body = inline_function_def.body

    ret_stmt = [stmt for stmt in function_body if isinstance(stmt, ast.Return)][0]
    function_body.remove(ret_stmt)
    retval = ret_stmt.value

    rhs_assignement = ast.Assign(targets=[ast.Name(id='rhs', ctx=ast.Store())], value=retval)

    call = ast.Call(func=ast.Name(id=function_name, ctx=ast.Store),
                    args=[ast.Name(id='_' + a + '_fresh', ctx=ast.Load()) for a in function_args], keywords=[])
    lhs_assignement = ast.Assign(targets=[ast.Name(id='lhs', ctx=ast.Store())], value=call)

    axiom_name = ast.Assign(targets=[ast.Name(id='axiom_name', ctx=ast.Store())],
                            value=ast.Str(function_name + '-inline'))

    axiom_str = astor.to_source(ast.Module(body=[axiom_name] + ann_assigns + fresh_vars_assigns + function_body +
                                                [lhs_assignement, rhs_assignement]))


    return axiom_str
