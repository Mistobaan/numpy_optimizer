from pysat.solvers import Minisat22
from pysat.formula import CNF
from pysat.pb import PBEnc
from epeg import create_vars_mappings
from peg_nodes import THETANode


def create_clauses(epeg):

    class_to_var, var_to_class, \
        class_pair_to_var, var_to_class_pair = create_vars_mappings(epeg)

    cnf = CNF(from_clauses=[])

    top_id = max(class_pair_to_var.values())

    # constraint (1) - at most one node from each class
    for class_name, class_nodes in epeg.classes.items():

        vars = [class_to_var[class_name]] + list(set([node.id for node in class_nodes]))
        weights = [1] + [-1 for _ in list(set([node.id for node in class_nodes]))]

        constraint_formula = PBEnc.equals(lits=vars, weights=weights, bound=0, top_id=top_id)
        top_id = max([top_id] + [abs(var) for clause in constraint_formula.clauses for var in clause])

        cnf.extend(constraint_formula.clauses)

    # constraint (2) - return class
    ret_class_var = class_to_var[epeg.root_class]
    return_constraint = PBEnc.equals(lits=[ret_class_var], weights=[1], bound=1, top_id=top_id)
    top_id = max([top_id] + [abs(var) for clause in return_constraint.clauses for var in clause])
    cnf.extend(return_constraint.clauses)

    # constraint (3) - taking node implies taking each of its children eq-classes
    for _id, node in epeg.nodes.items():
        # node => child_eq_class ---> ~node \/ child_eq_class
        cnf.extend([[-_id, class_to_var[child.eq_class]] for child in node.children])

    # constraint (4) - taking node implies taking pair of its class and each child class
    # (except for theta nodes' second child)
    for _id, node in epeg.nodes.items():
        for i in range(len(node.children)):
            if not (isinstance(node, THETANode) and i == 1):
                node_child_pair_var = class_pair_to_var[(node.eq_class, node.children[i].eq_class)]
                clause = [-_id, node_child_pair_var]
                cnf.append(clause)

    # constraint (5) - if there is pair of same class, there must be at least one theta node from that class taken
    for class_name, nodes in epeg.classes.items():
        pair_var = class_pair_to_var[(class_name, class_name)]
        clause = [-pair_var] + [node.id for node in nodes if isinstance(node, THETANode)]
        cnf.append(clause)


    # constraint (6) - transitivity
    for class_1 in epeg.classes.keys():
        for class_2 in epeg.classes.keys():
            for class_3 in epeg.classes.keys():
                if len(set([class_1, class_2, class_3])) == 3:
                    pair_1 = class_pair_to_var[(class_1, class_2)]
                    pair_2 = class_pair_to_var[(class_2, class_3)]
                    pair_3 = class_pair_to_var[(class_1, class_3)]
                    clause = [-pair_1, -pair_2, pair_3]
                    cnf.append(clause)


    return cnf, top_id


def optimize(epeg):

    constraints, top_id = create_clauses(epeg)
    upper_bound = epeg.start_peg_cost

    solver = None

    model, cost = _optimize(epeg, constraints, top_id, 0, upper_bound, solver)


    if model != None:
        for _id, node in epeg.nodes.items():

            if abs(_id) in [var for var in model if var >= 0]:
                for i in range(len(node.children)):

                    child_eq_class_id = node.children[i].eq_class
                    child_eq_class = epeg.classes[child_eq_class_id]
                    new_child_id = [node.id for node in child_eq_class if node.id in \
                                                [var for var in model if var >= 0]][0]
                    node.children[i] = epeg.nodes[new_child_id]

        root_id = [node.id for node in epeg.classes[epeg.root_class] if node.id in \
                                                        [var for var in model if var >= 0]][0]
        root = epeg.nodes[root_id]

        return root

    else:
        print('no solution')


def _optimize(epeg, constraints, top_id, lower_bound, upper_bound, model):

    if lower_bound <= upper_bound:

        cost = int((2 * lower_bound + upper_bound) / 3)

        lits = []
        weights = []
        for key, value in epeg.nodes.items():
            lits.append(key)
            weights.append(value.cost)

        object_function = PBEnc.leq(lits=lits, weights=weights,
                                   bound=cost, top_id=top_id)

        cnf = CNF(from_clauses=constraints.clauses + object_function.clauses)
        solver = Minisat22()
        solver.append_formula(cnf.clauses)

        if solver.solve():
            model = solver.get_model()
            return _optimize(epeg, constraints, top_id, lower_bound, cost - 1, model)
        else:
            return _optimize(epeg, constraints, top_id, cost + 1, upper_bound, model)


    return model, lower_bound

