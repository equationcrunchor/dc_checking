import sys
sys.path.append('cda_star')

from tpnsolver import *
from cda_star.propositional_state_logic import *
from cda_star.clauses import *
from cda_star.sat_solver import *
from dc_checking.dc_be import DCCheckerBE
from compute_relaxation import *
import heapq
import copy
from collections import Counter


class RelaxableTPNConstraint(TPNConstraint):
    def __init__(self, s, e, label=None, lb=None, ub=None, name=None, lb_relaxable=False, ub_relaxable=False, lb_lin_cost=0, ub_lin_cost=0):
        super().__init__(s, e, label=label, lb=lb, ub=ub, name=name)
        self.lb_relaxable = lb_relaxable
        self.ub_relaxable = ub_relaxable
        self.lb_lin_cost = lb_lin_cost
        self.ub_lin_cost = ub_lin_cost

class BCDRSolver(TPNSolver):
    def __init__(self, assignment_rewards):
        super().__init__(assignment_rewards)
        self.temporal_conflicts = {}

    def reset(self):
        super().reset()
        self.temporal_conflicts = {}

    def reward_func(self, assignments, relaxation):
        reward = 0
        for assignment in assignments:
            if assignment.var.name in self.assignment_rewards:
                reward += self.assignment_rewards[assignment.var.name].get(assignment.val, 0)
        if relaxation is not None:
            reward -= relaxation.objective_value
        return reward

    def add_to_priority_queue(self, assignments, decision_variables, relaxations=None, relaxed_conflicts = frozenset()):
        # Calculate the f(x) = g(x) + h(x), an admissible
        # heuristic for this assignment
        p = self.heuristic_func(assignments, decision_variables)
        if relaxations is not None:
            p -= relaxations.objective_value
        # Add to max priority queue (so negate)
        heapq.heappush(self.queue, (-p, assignments, relaxations, relaxed_conflicts))

    def is_complete_assignment(self, assignments, decision_variables):
        return decision_variables == set(assignment.var for assignment in assignments)

    def handle_conflict(self, conflict):
        print(" --> Nope! Got conflict {}".format(conflict))
        # Learn this conflict! Add it to self.known_conflicts (if appropriate)
        # Make sure no gamma already is more general then the conflict
        if any(gamma.issubset(conflict) for gamma in self.known_conflicts):
            return
        self.known_conflicts = [gamma for gamma in self.known_conflicts if not conflict.issubset(gamma)]
        self.known_conflicts.append(conflict)
        # self.queue = [(p, a, r, c) for (p, a, r, c) in self.queue if not manifests_conflict(a, conflict)]
        heapq.heapify(self.queue)


    def split_on_conflict(self, assignment, existing_relaxations, resolved_conflicts, new_conflict):
        """ Split on conflict, returning a list of neighboring states.

        Input: assignments - a frozenset of Assignment objects representing a partial assignment
               conflict - a frozenset of Assignment objects representing a conflict

        Output: A list of frozensets of Assignment objects, representing a list of neighboring
                states.
        """

        constituent_kernels = generate_constituent_kernels(new_conflict)
        neighbors = [(assignment | frozenset([ck]), existing_relaxations, resolved_conflicts) for ck in constituent_kernels]

        controllable, temporal_conflicts = self.check_temporal_consistency(assignment)
        if not controllable:
            new_relaxations = compute_relaxation(temporal_conflicts)
            conflicts = resolved_conflicts.union({new_conflict})
            if new_relaxations is not None:
                neighbors.append((assignment, new_relaxations, conflicts))
            else:
                self.temporal_conflicts[assignment] = temporal_conflicts

        neighbors = [a for a in neighbors if is_self_consistent(a[0])]
        return neighbors

    def resolve_known_conflicts(self, assignment, relaxations, resolved_conflicts):
        for conflict in self.known_conflicts:
            if manifests_conflict(assignment, conflict) and conflict not in resolved_conflicts:
                return conflict
        return None

    def check_temporal_consistency(self, assignment, relaxations=None):
        active_constraints = [constraint for constraint in self.temporal_constraints if constraint.is_activated(assignment)]
        if relaxations is not None:
            relaxed_constraints = []
            for constraint in active_constraints:
                relaxed_constraint = copy.copy(constraint)
                if (constraint, 'LB-') in relaxations.sol:
                    relaxed_constraint.lb -= relaxations.sol[(constraint, 'LB-')]
                if (constraint, 'UB+') in relaxations.sol:
                    relaxed_constraint.ub += relaxations.sol[(constraint, 'UB+')]
                relaxed_constraints.append(relaxed_constraint)
            network = TemporalNetwork(relaxed_constraints)
        else:
            network = TemporalNetwork(active_constraints)
        checker = DCCheckerBE(network)
        return checker.is_controllable(visualize=False, visualize_conflict=False)

    def run(self):
        """ Split on conflict, returning a list of neighboring states.

        Output: An assignment to all decision variables, represented as a frozenset of
                Assignment objects (note that only decision variables should be assigned).
                The returned result should be the optimal solution to the CSP. If no solution
                exists, returns None.
        """
        # Set up
        self.reset()
        self.sat_solver = SATSolver(self)
        decision_variables = self.get_decision_variables()
        self.add_to_priority_queue(frozenset(), decision_variables)
        while len(self.queue) > 0:
            p, assignment, relaxations, resolved_conflicts = heapq.heappop(self.queue)
            print("Popped {} with p={}".format(assignment, -p))

            current_conflict = self.resolve_known_conflicts(assignment, relaxations, resolved_conflicts)

            if current_conflict is None:
                if self.is_complete_assignment(assignment, decision_variables):
                    print(" --> Checking consistency")
                    print(" --> Checking boolean consistency")
                    consistent, a, conflict = self.sat_solver.check_consistency(assignment)
                    if not consistent:
                        self.handle_conflict(conflict)
                    else:
                        print(" --> Checking temporal consistency")
                        controllable, temporal_conflicts = self.check_temporal_consistency(assignment, relaxations)
                        if not controllable:
                            # self.temporal_conflicts.append((assignment, temporal_conflicts))
                            for temporal_conflict in temporal_conflicts:
                                conflict = set()
                                for constraint, boundtype in temporal_conflict:
                                    variables = constraint.get_variables()
                                    for var in variables:
                                        for assign in assignment:
                                            if var.name == assign.var.name:
                                                conflict.add(assign)
                            self.handle_conflict(frozenset(conflict))
                            self.add_to_priority_queue(assignment, decision_variables, relaxations, resolved_conflicts)
                        else:
                            print(" --> Yep! Done.")
                            return True, self.reward_func(assignment, relaxations), assignment, relaxations, self.temporal_conflicts.copy()

                else:
                    # assignment is not a full assignment
                    print(" --> Splitting on \033[32mvariable\033[0m")
                    var = choose_variable_to_split_on(assignment, decision_variables)
                    neighbors = self.split_on_variable(assignment, var)
                    # Add neighbors to the self.queue
                    for neigh in neighbors:
                        print(" --> Adding {}".format(neigh, relaxations, resolved_conflicts))
                        self.add_to_priority_queue(neigh, decision_variables, relaxations, resolved_conflicts)
            else:
                print(" --> Splitting on \033[31mconflict\033[0m] {}".format(current_conflict))
                neighbors = self.split_on_conflict(assignment, relaxations, resolved_conflicts, current_conflict)
                # Add neighbors to the self.queue
                for neigh, relaxation, conflicts in neighbors:
                    print(" --> Adding {}".format((neigh, relaxation, conflicts)))
                    self.add_to_priority_queue(neigh, decision_variables, relaxation, conflicts)

        # If we get here, no assignments found!
        return False, None, None, None, self.temporal_conflicts.copy()

if __name__ == '__main__':
    # testing
    constraints = [
        RelaxableTPNConstraint('e1', 'e2', None, 300, 400, 'c1', ub_relaxable=True, ub_lin_cost=1),
        TPNConstraint('e1', 'e3', None, 0, 0, 'c2'),
        TPNConstraint('e3', 'e4', None, 0, 0, 'c3'),
        RelaxableTPNConstraint('e4', 'e5', 'path_choice=one', 405, 486, 'c4', lb_relaxable=False, lb_lin_cost=0.5),
        TPNConstraint('e5', 'e8', None, 0, 0, 'c5'),
        TPNConstraint('e3', 'e6', None, 0, 0, 'c6'),
        TPNConstraint('e6', 'e7', 'path_choice=two', 405, 486, 'c7'),
        TPNConstraint('e7', 'e8', None, 0, 0, 'c8'),
        TPNConstraint('e8', 'e9', None, 0, 0, 'c9'),
        RelaxableTPNConstraint('e9', 'e10', 'proceed=ok', 100, 200, 'c10', lb_relaxable=False, lb_lin_cost=0.5),
        TPNConstraint('e10', 'e13', None, 0, 0, 'c11'),
        TPNConstraint('e8', 'e11', None, 0, 0, 'c12'),
        TPNConstraint('e11', 'e12', 'proceed=not_ok', 0, 2, 'c13'),
        TPNConstraint('e12', 'e13', None, 0, 0, 'c14'),
        TPNConstraint('e13', 'e2', None, 0, 0, 'c15'),
    ]

    assignment_rewards = {'path_choice': {'one': 10, 'two': 0}, 'proceed': {'ok': 1000, 'not_ok': 0}}

    prob = BCDRSolver(assignment_rewards)
    prob.add_variable('path1', type='finite_domain', domain=['ok', 'not_ok'], decision_variable=True)
    prob.add_variable('path2', type='finite_domain', domain=['ok', 'not_ok'], decision_variable=True)
    prob.add_variable('proceed', type='finite_domain', domain=['ok', 'not_ok'], decision_variable=True)
    prob.add_variable('path_choice', type='finite_domain', domain=['one', 'two'], decision_variable=True)
    prob.add_constraint('path1=ok')
    prob.add_constraint('path2=ok')
    # prob.add_constraint('proceed=ok')
    prob.add_constraint('path1=not_ok => ~(path_choice=one)')
    prob.add_constraint('path2=not_ok => ~(path_choice=two)')
    for constraint in constraints:
        prob.add_temporal_constraint(constraint)
    # print("Solution:", prob.run())
    solvable, reward, assignments, relaxations, conflicts = prob.run()

    print("Known conflicts:", prob.known_conflicts)
    c = Counter()
    largest_intersection = None
    for assignment, conflict in conflicts.items():
        print("")
        print(assignment)
        for conflict in conflict:
            print(conflict)
            if largest_intersection is None:
                largest_intersection = set((constraint.name, bt) for constraint, bt in conflict)
            else:
                largest_intersection = largest_intersection.intersection((constraint.name, bt) for constraint, bt in conflict)
            for constraint, bt in conflict:
                c[(constraint.name, bt)] += 1
    print("")
    print(c)
    print(largest_intersection)

    print("\nSolution:", reward, assignments, relaxations)
