from clips_utils import clips_node_to_node_info, node_from_type_info
import peg_nodes
import ast
import pickle
import numpy as np
from peg_nodes import LeafNode
from sklearn.preprocessing import normalize



class EPEG(object):

    def __init__(self, peg):
        self.classes = {}
        self.nodes = {}
        self.root_class = self.initialize_epeg(peg)
        # change cost
        self.start_peg_cost = sum([node.cost for node in self.nodes.values()])
        self.current_node_id = max(self.nodes.keys()) + 1

    def compute_node_id(self):
        self.current_node_id += 1
        return self.current_node_id

    def compute_predecessors(self):

        for node in self.nodes.values():
            node.predecessors = []

        for node in self.nodes.values():
            for child in node.children:
                child.predecessors.append(node)

    def compute_predecessors_helper(self, node, visited):

        if node.id in visited:
            return

        visited.append(node.id)

        for child in node.children:
            child.predecessors.append(node)
            self.compute_predecessors_helper(child, visited)

    def get_unique_node(self, node):

        same_nodes = [n for n in self.nodes.values() if n.same(node)]

        if len(same_nodes) > 0:
            return same_nodes[0]

        return node

    def add_node_to_eq_class(self, node, eq_class):

        assert (node.eq_class == eq_class)

        if not eq_class in self.classes.keys():
            self.classes[eq_class] = [node]


        else:
            if not node in self.classes[eq_class]:
                self.classes[eq_class].append(node)


    def remove_node_from_eq_class(self, node, eq_class):

        assert(node.eq_class == eq_class)

        self.classes[eq_class].remove(node)

        if len(self.classes[eq_class]) == 0:
            del self.classes[eq_class]


    def replace_node(self, old_node, new_node):

        new_node = self.get_unique_node(new_node)

        if old_node.eq_class == self.root_class:
            self.root_class = new_node.eq_class

        for pred in old_node.predecessors:
            pred.children = [ch if ch.id != old_node.id else new_node for ch in pred.children]
            new_node.predecessors.append(pred)

        del self.nodes[old_node.id]
        self.remove_node_from_eq_class(old_node, old_node.eq_class)

        self.nodes[new_node.id] = new_node
        self.add_node_to_eq_class(new_node, new_node.eq_class)

        if old_node.eq_class != new_node.eq_class and old_node.eq_class in self.classes.keys():

            if new_node.eq_class.find('class') >= 0:
                for node in self.classes[old_node.eq_class]:
                    if not node in self.classes[new_node.eq_class]:
                        node.eq_class = new_node.eq_class
                        self.classes[new_node.eq_class].append(node)

            # constant class case
            else:
                for node in self.classes[old_node.eq_class]:
                    for pred in node.predecessors:
                        pred.children = [c if c.id != node.id else new_node for c in pred.children]
                    del self.nodes[node.id]

            del self.classes[old_node.eq_class]


    def initialize_epeg(self, peg):

        self.initialize_epeg_helper(peg.root)

        return peg.root.eq_class

    def initialize_epeg_helper(self, node):

        if node.id in self.nodes.keys():
            return

        self.nodes[node.id] = node

        if node.eq_class not in self.classes.keys():
            self.classes[node.eq_class] = [node]
        else:
            if not node in self.classes[node.eq_class]:
                self.classes[node.eq_class].append(node)

        for child in node.children:
            self.initialize_epeg_helper(child)

    def filter_reachable_classes(self):

        reachable_classes = []

        self.filter_reachable_classes_helper(self.root_class, reachable_classes)
        unreachable_classes = [eq_cl for eq_cl in self.classes.keys() if eq_cl not in reachable_classes]

        for eq_class in unreachable_classes:

            for node in self.classes[eq_class]:
                del self.nodes[node.id]

            del self.classes[eq_class]

    def filter_reachable_classes_helper(self, eq_class, visited):

        if eq_class in visited:
            return

        visited.append(eq_class)

        for node in self.classes[eq_class]:
            for child in node.children:
                self.filter_reachable_classes_helper(child.eq_class, visited)

    def saturate(self, env, equalities):

        for instance in env.instances():

            clp_node = clips_node_to_node_info(str(instance))

            if clp_node != None:
                _id, eq_class, type_name, args, loop_depth = clp_node[:5]

                eq_class = map_to_eq_class(eq_class, equalities)
                assert(eq_class != None)

                if int(_id) >= 0:
                    if eq_class != self.nodes[int(_id)].eq_class:
                        self.classes[self.nodes[int(_id)].eq_class].remove(self.nodes[int(_id)])
                        self.nodes[int(_id)].eq_class = eq_class

                        if eq_class in self.classes.keys() and not self.nodes[int(_id)] in self.classes[eq_class]:
                            self.classes[eq_class].append(self.nodes[int(_id)])
                        else:
                            self.classes[eq_class] = [self.nodes[int(_id)]]
                    continue

                _id = -int(_id)
                self.nodes[_id] = node_from_type_info(_id, eq_class, type_name, args, loop_depth)

                if eq_class not in self.classes.keys():
                    self.classes[eq_class] = [self.nodes[_id]]
                else:
                    if not self.nodes[_id] in self.classes[eq_class]:
                        self.classes[eq_class].append(self.nodes[_id])

        for instance in env.instances():

            clp_node = clips_node_to_node_info(str(instance))

            if clp_node != None:

                _id = int(clp_node[0])

                if _id >= 0:
                    continue

                node_children_eq_classes = [map_to_eq_class(eq_class, equalities) for eq_class in clp_node[5:]]

                _id = -_id
                # setting node children to first members of their eq-classes
                self.nodes[_id].children = [self.classes[child_class][0] if _id != self.classes[child_class][0].id
                                            else self.classes[child_class][-1]
                                            for child_class in node_children_eq_classes]

        file_content = open('clips_data.txt', 'r')
        from clips_utils import get_lhs_rhs_node_ids_from_line

        inlined_nodes = []

        for line in file_content.readlines():
            axiom_name, lhs_ids, rhs_ids = get_lhs_rhs_node_ids_from_line(line)

            if axiom_name.endswith('-inline'):
                inlined_nodes += rhs_ids

            if axiom_name in ['constant-step-loop-addition', 'determinant-of-inverse']:
              #  predict_nodes_cost(lhs_ids, rhs_ids, axiom_name, self, inlined_nodes)
                pass
            else:

                left_root_id = abs(lhs_ids[0])
                right_root_id = -rhs_ids[0]

                if not left_root_id in self.nodes.keys() or not right_root_id in self.nodes.keys():
                    continue

                left_root = self.nodes[left_root_id]
                right_root = self.nodes[right_root_id]

                if left_root.type_name() == right_root.type_name():
                    if set([ch.eq_class for ch in left_root.children]) == set([ch.eq_class for ch in right_root.children]):
                        right_root.cost = left_root.cost


def add_equality(pair, equalities):

    fst = pair[0]
    snd = pair[1]

    if fst == snd:
        return

    if fst in equalities.keys() and snd in equalities.keys():
        for val in equalities[snd]:
            equalities[fst].append(val)
        equalities[fst].append(snd)
        del equalities[snd]

    elif fst in equalities.keys():
        equalities[fst].append(snd)

    elif snd in equalities.keys():
        equalities[snd].append(fst)

    else:

        for k, values in equalities.items():
            if fst in values:
                equalities[k].append(snd)
                break
            if snd in values:
                equalities[k].append(fst)
                break
        else:
            equalities[fst] = [snd]


def map_to_eq_class(class_name, equalities):

    if class_name in equalities.keys():
        return class_name

    for k, values in equalities.items():
        if class_name in values:
            return k

    return class_name


def create_vars_mappings(epeg):

    current_var = max(epeg.nodes.keys()) + 1
    class_to_var = {}
    var_to_class = {}

    for class_name in epeg.classes.keys():
        class_to_var[class_name] = current_var
        var_to_class[current_var] = class_name
        current_var += 1

    class_pair_to_var = {}
    var_to_class_pair = {}

    for fst_class in epeg.classes.keys():
        for snd_class in epeg.classes.keys():
            class_pair_to_var[(fst_class, snd_class)] = current_var
            var_to_class_pair[current_var] = (fst_class, snd_class)
            current_var += 1

    return class_to_var, var_to_class, class_pair_to_var, var_to_class_pair


def predict_nodes_cost(lhs_nodes, rhs_nodes, axiom_name, epeg, inlined_nodes):

    model = pickle.load(open('models/' + axiom_name + '_model.sav', 'rb'))

    x = np.array([epeg.nodes[abs(node_id)].cost for node_id in lhs_nodes]).reshape(1, -1)
    x = normalize(x)
    costs = model.predict(x).ravel()


    for node_id, cost in zip(rhs_nodes, costs):

        if node_id in inlined_nodes:
            continue

        if node_id < 0 and -node_id in epeg.nodes.keys() and not isinstance(epeg.nodes[-node_id], LeafNode):
            epeg.nodes[-node_id].cost = int(cost) if cost > 0 else 0


