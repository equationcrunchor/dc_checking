import sys
sys.path.append('cda_star')

from dc_checking.temporal_network import TemporalNetwork, SimpleContingentTemporalConstraint, SimpleTemporalConstraint
from cda_star.propositional_state_logic import *
from cda_star.clauses import *
from cda_star.sat_solver import *
import heapq
from dc_checking.dc_be import DCCheckerBE


def is_self_consistent(assignments):
    # Can't have multiple values assigned to a single variable! So if number of
    # distinct variables is less than number of distinct assignments, it's not consistent.
    return len(assignments) == len(frozenset(assignment.var for assignment in assignments))


def manifests_conflict(assignments, conflict):
    """Checks to see if assignments manifests the conflict.

    Input: assignments - a frozenset of Assignment objects representing
           conflict - a frozenset of Assignment objects representing a conflict
    Output: True or False
    """
    return conflict.issubset(assignments)


def resolves_conflict(assignments, conflict):
    """Checks to see if assignments resolves the conflict.

    Input: assignments - a frozenset of Assignment objects representing
           conflict - a frozenset of Assignment objects representing a conflict
    Output: True or False
    """
    return not(is_self_consistent(assignments | conflict))


def generate_constituent_kernels(conflict):
    """ Helper function to generate constituent kernels
    conflict is a frozenset of assignments"""
    constituent_kernels = []
    for assignment in conflict:
        for di in (assignment.var.domain - frozenset([assignment.val])):
            constituent_kernels.append(assignment.var.get_assignment(di))
    return constituent_kernels


def choose_variable_to_split_on(assignments, decision_variables):
    """ Choose an unassigned variable to split on.

        Input: assignments - a frozenset of Assignment objects
               decision_variables - a frozenset of all the decision variables"""
    vars_unassigned = decision_variables - frozenset(assignment.var for assignment in assignments)
    return list(vars_unassigned)[0]


class TPNConstraint(SimpleTemporalConstraint):
    def __init__(self, s, e, label=None, lb=None, ub=None, name=None):
        super().__init__(s, e, lb=lb, ub=ub, name=name)
        self.expr_parser = get_formula_parser()
        self.str_label = label
        self.label = None
        if self.str_label is not None:
            self.cnf_gen = CNFGenerator()

    def is_activated(self, assignments):
        if self.label is None:
            return True
        cnf = self.cnf_gen.convert_expressions_to_cnf([self.label])
        assignments = [Literal(assignment, True) for assignment in assignments]
        for clause in cnf:
            if not clause.is_satisfied_by_assignments(assignments):
                return False
        return True

    def get_variables(self):
        if self.label is None:
            return frozenset()
        variables = set()
        cnf = self.cnf_gen.convert_expressions_to_cnf([self.label])
        for clause in cnf:
            for literal in clause.literals:
                variables.add(literal.atom.var)
        return variables

    def copy(self):
        copy = cls(self.s, self.e, self.str_label, self.lb, self.ub, self.name)
        copy.label = self.label
        return copy


class TPNSolver(Problem):
    def __init__(self, reward_func):
        super().__init__()
        self.temporal_constraints = []
        self.candidate = None
        self.queue = []
        self.known_conflicts = []
        self.reward_func = reward_func
        self.expanded = set()

    def add_temporal_constraint(self, constraint):
        if constraint.str_label is not None:
            m = self.parse_expression(constraint.str_label)
            constraint.label = m
        self.temporal_constraints.append(constraint)

    def add_to_priority_queue(self, assignments, decision_variables):
        # Calculate the f(x) = g(x) + h(x), an admissible
        # heuristic for this assignment
        p = self.reward_func(assignments, decision_variables)
        # Add to max priority queue (so negate)
        heapq.heappush(self.queue, (-p, assignments))

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
        # Remove assignments from self.queue manifesting this conflict
        self.queue = [(p, a) for (p, a) in self.queue if not manifests_conflict(a, conflict)]
        heapq.heapify(self.queue)

    def split_on_variable(self, assignments, variable):
        """ Split on variable, returning a list of neighboring states.

        Input: assignments - a frozenset of Assignment objects representing a partial assignment
               variable - a variable, not represented by an Assignment in assignments, on
                          which to split via its domainv values.

        Output: A list of frozensets of Assignment objects, representing a list of neighboring
                states.
        """
        neighbors = [(assignments | frozenset([variable.get_assignment(di)])) for di in variable.domain]
        return neighbors


    def split_on_conflict(self, assignments, conflict):
        """ Split on conflict, returning a list of neighboring states.

        Input: assignments - a frozenset of Assignment objects representing a partial assignment
               conflict - a frozenset of Assignment objects representing a conflict

        Output: A list of frozensets of Assignment objects, representing a list of neighboring
                states.
        """

        constituent_kernels = generate_constituent_kernels(conflict)
        neighbors = [(assignments | frozenset([ck])) for ck in constituent_kernels]
        neighbors = [a for a in neighbors if is_self_consistent(a)]
        return neighbors

    def run(self):
        """ Split on conflict, returning a list of neighboring states.

        Output: An assignment to all decision variables, represented as a frozenset of
                Assignment objects (note that only decision variables should be assigned).
                The returned result should be the optimal solution to the CSP. If no solution
                exists, returns None.
        """
        # Set up
        self.sat_solver = SATSolver(self)
        decision_variables = self.get_decision_variables()
        self.add_to_priority_queue(frozenset(), decision_variables)
        while len(self.queue) > 0:
            # print self.queue
            p, assignment = heapq.heappop(self.queue)
            print("Popped {} with p={}".format(assignment, -p))
            self.expanded.add(assignment)
            self.queue = [(p, a) for (p, a) in self.queue if a != assignment] # Optional: remove any identical from self.queue

            if self.is_complete_assignment(assignment, decision_variables):
                print(" --> Checking consistency")
                print(" --> Checking boolean consistency")
                consistent, a, conflict = self.sat_solver.check_consistency(assignment)
                if not consistent:
                    self.handle_conflict(conflict)
                else:
                    print(" --> Checking temporal consistency")
                    active_constraints = [constraint for constraint in self.temporal_constraints if constraint.is_activated(assignment)]
                    network = TemporalNetwork(active_constraints)
                    checker = DCCheckerBE(network)
                    controllable, temporal_conflicts = checker.is_controllable(visualize=False, visualize_conflict=False)
                    # print("TEMPORAL CONFLICT:", temporal_conflicts)
                    if not controllable:
                        for temporal_conflict in temporal_conflicts:
                            conflict = set()
                            for constraint, annotation in temporal_conflict:
                                variables = constraint.get_variables()
                                for var in variables:
                                    for assign in assignment:
                                        if var.name == assign.var.name:
                                            conflict.add(assign)
                            self.handle_conflict(conflict)
                    else:
                        print(" --> Yep! Done.")
                        return assignment # Use yield to make a generator and keep enumerating!!

            else:
                # assignment is not a full assignment

                if all(resolves_conflict(assignment, gamma) for gamma in self.known_conflicts):
                    print(" --> Splitting on \033[32mvariable\033[0m")
                    var = choose_variable_to_split_on(assignment, decision_variables)
                    neighbors = self.split_on_variable(assignment, var)
                else:
                    gamma = next(g for g in self.known_conflicts if not(resolves_conflict(assignment, g)))
                    print(" --> Splitting on \033[31mconflict\033[0m] {}".format(gamma))
                    neighbors = self.split_on_conflict(assignment, gamma)

                # Add neighbors to the self.queue
                for neigh in neighbors:
                    if neigh not in self.expanded:
                        print(" --> Adding {}".format(neigh))
                        self.add_to_priority_queue(neigh, decision_variables)

        # If we get here, no assignments found!
        return None


if __name__ == '__main__':
    # testing
    constraints = [
        TPNConstraint('e1', 'e2', None, 450, 540, 'c1'),
        TPNConstraint('e1', 'e3', None, 0, 0, 'c2'),
        TPNConstraint('e3', 'e4', None, 0, 0, 'c3'),
        TPNConstraint('e4', 'e5', 'path_choice=one', 405, 486, 'c4'),
        TPNConstraint('e5', 'e8', None, 0, 0, 'c5'),
        TPNConstraint('e3', 'e6', None, 0, 0, 'c6'),
        TPNConstraint('e6', 'e7', 'path_choice=two', 405, 486, 'c7'),
        TPNConstraint('e7', 'e8', None, 0, 0, 'c8'),
        TPNConstraint('e8', 'e9', None, 0, 0, 'c9'),
        TPNConstraint('e9', 'e10', 'proceed=ok', 0, 0, 'c10'),
        TPNConstraint('e10', 'e13', None, 0, 0, 'c11'),
        TPNConstraint('e8', 'e11', None, 0, 0, 'c12'),
        TPNConstraint('e11', 'e12', None, 0, 2, 'c13'),
        TPNConstraint('e13', 'e2', None, 0, 0, 'c14'),
    ]

    def reward_func(assignments, decision_variables):
        for assignment in assignments:
            if assignment.var.name == 'path_choice' and assignment.val == 'one':
                return 10
        return 0

    prob = TPNSolver(reward_func)
    prob.add_variable('path1', type='finite_domain', domain=['ok', 'not_ok'], decision_variable=True)
    prob.add_variable('path2', type='finite_domain', domain=['ok', 'not_ok'], decision_variable=True)
    prob.add_variable('proceed', type='finite_domain', domain=['ok', 'not_ok'], decision_variable=True)
    prob.add_variable('path_choice', type='finite_domain', domain=['one', 'two'], decision_variable=True)
    prob.add_constraint('path1=ok')
    prob.add_constraint('path2=ok')
    prob.add_constraint('proceed=ok')
    prob.add_constraint('path1=not_ok => ~(path_choice=one)')
    prob.add_constraint('path2=not_ok => ~(path_choice=two)')
    for constraint in constraints:
        prob.add_temporal_constraint(constraint)
    print("Solution:", prob.run())
