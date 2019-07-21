from peg_builder import compute_peg, get_nodes
from profiler import generate_tac_code, profile
from sklearn import model_selection, preprocessing
from sklearn import metrics
from sklearn.ensemble import RandomForestRegressor
import ast
import numpy as np
import pickle


def create_datasets(param_list):

    file_content = open("compute_models.py").read()
    tree_init = ast.parse(file_content)

    generate_tac_code(tree_init)
    line_durations = profile([str(i) for i in param_list])

    f = open('tac.py', 'r')
    src = f.read()
    tree = ast.parse(src)

    lhs_func = [stmt for stmt in tree.body if isinstance(stmt, ast.FunctionDef) and stmt.name == 'lhs'][0]
    rhs_func = [stmt for stmt in tree.body if isinstance(stmt, ast.FunctionDef) and stmt.name == 'rhs'][0]

    lhs_peg = compute_peg(lhs_func, line_durations)
    rhs_peg = compute_peg(rhs_func, line_durations)

    lhs_nodes_costs = [node.cost for node in get_nodes(lhs_peg.root)]
    rhs_nodes_costs = [node.cost for node in get_nodes(rhs_peg.root)]

    return lhs_nodes_costs, rhs_nodes_costs



def main():


    lhs_costs = []
    rhs_costs = []

    for i in list(range(1, 100)):

        lhs_nodes_costs, rhs_nodes_costs = create_datasets([i])

        lhs_costs.append(lhs_nodes_costs)
        rhs_costs.append(rhs_nodes_costs)



    X = np.array(lhs_costs)
    y = np.array(rhs_costs)

    X_train, X_test, y_train, y_test = model_selection.train_test_split(X, y, test_size=0.4)

    X_train = preprocessing.normalize(X_train)
    X_test = preprocessing.normalize(X_test)


    scores = []
    params = list(range(5, 30))

    for n in params:

        regr = RandomForestRegressor(n_estimators=n)
        regr.fit(X_train, y_train)
        predicted = regr.predict(X_test)
        score = metrics.r2_score(y_test, predicted)
        scores.append(score)

    print('scores:', scores)
    best_n_idx = np.argmax(np.array(scores))
    best_n = params[best_n_idx]
    print(best_n)
    regr = RandomForestRegressor(n_estimators=n)
    regr.fit(preprocessing.normalize(X), y)


    print('\nscore:')
    print(metrics.r2_score(y_test, regr.predict(X_test)))

    print('\nx train:')
    print(X_train)

    print('\ny train:')
    print(y_train)

    print('\ny_predicted:')
    print(np.array(regr.predict(X_test), dtype='int'))

    print('\ny_test:')
    print(y_test)

    axiom_name = 'determinant-of-inverse'
    filename = 'models/' + axiom_name + '_model.sav'
    pickle.dump(regr, open(filename, 'wb'))



main()