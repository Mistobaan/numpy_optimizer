import clips
import ast
from peg_builder import compute_peg, compute_axiom_peg
from inlining import ax_format_to_funcdef
from clips_utils import create_rule, peg_to_instances
from epeg import EPEG, add_equality, map_to_eq_class
from peg2code import CodeFromPEGGenerator
from optimization_utils import filter_constant_classes, apply_constant_folding, remove_useless_evals
from broadcast import apply_broadcasting
from common_graph_funcs import render


def is_optimizable(func_def):

    assert(isinstance(func_def, ast.FunctionDef))
    return len([dec for dec in func_def.decorator_list if isinstance(dec, ast.Name) and dec.id == 'opt'])


def optimize(func_def, axiom_srcs, line_durations):

    peg = compute_peg(func_def, line_durations)

    print('Optimizing ' + func_def.name + '...')

    render(peg.root, 'peg_' + func_def.name)

    env = clips.Environment()

    env.eval('(open "clips_data.txt" output-file "w")')
    env.strategy = clips.Strategy.BREADTH

    env.eval('(load "clips_constructs.clp")')

    # env.eval('(watch facts)')
    #env.eval('(watch activations)')
    #env.eval('(watch instances)')

    for i in range(len(axiom_srcs)):
        ax_func_def_format = ax_format_to_funcdef(axiom_srcs[i])
        axiom_peg = compute_axiom_peg(ax_func_def_format, name='ax_' + str(i))
        rule = create_rule(axiom_peg)
        env.build(rule)

    instances = peg_to_instances(peg)
    for instance in instances.splitlines():
        env.eval(instance)

  #  print('FACTS================================')
  #  for f in env.facts():
   #     print(str(f))

    print('RULES================================')
    for r in env.rules():
        print(r)

    env.run(1000)

    print('INSTANCES================================')
    for i in env.instances():
        print(i)

    epeg = EPEG(peg)

    clips_data_file = open('clips_data.txt', 'r')
    equalities = {}

    for line in clips_data_file.readlines():
        pair = tuple(line.split()[1:3])
        add_equality(pair, equalities)

    epeg.saturate(env, equalities)

    env.eval('(close)')

    epeg.root_class = map_to_eq_class(epeg.root_class, equalities)

    epeg.compute_predecessors()

    filter_constant_classes(epeg)
    apply_constant_folding(epeg)
    apply_broadcasting(epeg)
    apply_constant_folding(epeg)
    remove_useless_evals(epeg)

    epeg.filter_reachable_classes()

    import graphviz
    g = graphviz.Digraph(name='epeg_' + func_def.name, format='png', strict=False)

    for k, v in epeg.classes.items():

        with g.subgraph(name='cluster_' + k) as c:

            for node in v:
                c.node(str(node.id), label=str(node) + ' (cost ' + str(node.cost) + ')')
                for child in node.children:
                    g.edge(str(node.id), str(child.id))
            c.attr(label=k)
            c.attr(color='green')

    g.view()

    import solver

    start_cost = epeg.start_peg_cost
    root = solver.optimize(epeg)

    render(root, 'peg_opt' + func_def.name)

    assert root != None

    from peg_builder import get_nodes
    peg.ctx = {'retvar' : root}
    peg.root = root
    peg.nodes = get_nodes(root)

    if sum([n.cost for n in peg.nodes]) == start_cost:
        return None

    gen = CodeFromPEGGenerator(peg)

    code = gen.get_code()

    return code
