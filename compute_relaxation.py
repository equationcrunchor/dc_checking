import gurobipy as gp
from gurobipy import GRB
from uuid import uuid4

MAX_NUMERIC_BOUND = 100000
ROUND_DIGITS = 3
NUMERIC_STABLE_EPSILON = 0.0001


class Relaxation:
    def __init__(self, sol, objective_value):
        self.sol = sol
        self.objective_value = objective_value

    def __str__(self):
        return f"<Relaxation: {self.sol}, Objective: {self.objective_value}>"

    def __repr__(self):
        return f"Relaxation({self.sol}, {self.objective_value})"

    def __add__(self, other):
        new_sol = self.sol.copy()
        for constraint, boundtype in other.sol.keys():
            if (constraint, boundtype) in new_sol.keys():
                new_sol[(constraint, boundtype)] = max(new_sol[(constraint, boundtype)], other.sol[new_sol[(constraint, boundtype)]])
        new_cost = 0
        for constraint, boundtype in new_sol.keys():
            relax_amount = new_sol[(constraint, boundtype)]
            if boundtype == 'LB-':
                coeff = constraint.lb_lin_cost
            elif boundtype == 'UB+':
                coeff = constraint.ub_lin_cost
            new_cost += coeff * relax_amount

        return Relaxation(new_sol, new_cost)

    def __eq__(self, other):
        return self.sol == other.sol


def compute_relaxation(conflicts, relaxation_var=None):

    # Create a new model
    m = gp.Model('relaxation')
    m.setParam('OutputFlag', False)

    # Create a mapping for variables
    var_map = {}

    # Add market objectives from master
    objective_expr = gp.LinExpr()
    # add_market_objectives_to_objective_expr(m, objective_expr, relaxation_var, price_vector, var_map)

    # Add conflicts
    add_conflicts_to_model(m, objective_expr, conflicts, var_map)

    # Set objective
    m.setObjective(objective_expr, GRB.MINIMIZE)

    # Optimize model
    m.optimize()

    if m.status == GRB.Status.INFEASIBLE:
        return None
    else:
        objective_value = m.objVal
        sol = {}
        print(m)
        for var in var_map:
            sol[var] = round(var_map[var].x, ROUND_DIGITS)
        return Relaxation(sol, objective_value)

class LinearConstraint:

    def __init__(self, name, variable_coeffs=None, lb=None, ub=None):
        if variable_coeffs is None:
            variable_coeffs = {}
        self.name = name
        self.variable_coeffs = variable_coeffs
        self.lb = lb
        self.ub = ub

    def __repr__(self):
        return "<LinConstr {}: {}, lb: {}, ub: {}>".format(self.name, self.variable_coeffs, self.lb, self.ub)

    def __str__(self):
        return "<LinConstr {}: {}, lb: {}, ub: {}>".format(self.name, self.variable_coeffs, self.lb, self.ub)

    def canonicalize(self):
        """
        Canonicalize the constraint by converting to Ax <= b (upper bound)
        """
        # Do not handle when both lb and ub is set
        assert(self.lb is None or self.ub is None)
        if self.lb is not None:
            self.ub = - self.lb
            self.lb = None
            self.variable_coeffs = {key: -value for key, value in self.variable_coeffs.items()}

    def canonicalize_lb(self):
        """
        Canonicalize the constraint by converting to Bx >= c (lower bound)
        """
        # Do not handle when both lb and ub is set
        assert(self.lb is None or self.ub is None)
        if self.ub is not None:
            self.lb = - self.ub
            self.ub = None
            self.variable_coeffs = {key: -value for key, value in self.variable_coeffs.items()}


def conflict_to_linconstr(conflict):
    linconstrs = []
    variable_coeffs = {}
    total_sum = 0
    for term in conflict:
        constraint = term[0]
        is_relaxable = False
        # The following should be fixed... I changed how to annotate relaxation in between and
        # hasn't fixed this
        if 'lb_relaxable' in constraint.annotation or 'ub_relaxable' in constraint.annotation:
            constraint.lb_relaxable = constraint.annotation['lb_relaxable']
            constraint.ub_relaxable = constraint.annotation['ub_relaxable']
            constraint.lb_lin_cost = constraint.annotation['lb_lin_cost']
            constraint.ub_lin_cost = constraint.annotation['ub_lin_cost']
        if hasattr(constraint, "lb_relaxable") or hasattr(constraint, "ub_relaxable"):
            is_relaxable = True
        for boundtype in term[1:]:
            if boundtype == "UB+":
                total_sum += constraint.ub
                if is_relaxable:
                    if constraint.ub_relaxable:
                        if (constraint, "UB+") not in variable_coeffs:
                            variable_coeffs[(constraint, "UB+")] = 1
                        else:
                            variable_coeffs[(constraint, "UB+")] += 1
            elif boundtype == "UB-":
                total_sum += -constraint.ub
                if is_relaxable:
                    if constraint.ub_relaxable:
                        if (constraint, "UB+") not in variable_coeffs:
                            variable_coeffs[(constraint, "UB+")] = -1
                        else:
                            variable_coeffs[(constraint, "UB+")] -= 1
            elif boundtype == "LB+":
                total_sum += constraint.lb
                if is_relaxable:
                    if constraint.lb_relaxable:
                        if (constraint, "LB-") not in variable_coeffs:
                            variable_coeffs[(constraint, "LB-")] = -1
                        else:
                            variable_coeffs[(constraint, "LB-")] -= 1
            elif boundtype == "LB-":
                total_sum += -constraint.lb
                if is_relaxable:
                    if constraint.lb_relaxable:
                        if (constraint, "LB-") not in variable_coeffs:
                            variable_coeffs[(constraint, "LB-")] = 1
                        else:
                            variable_coeffs[(constraint, "LB-")] += 1
            else:
                raise ValueError
    linconstr = LinearConstraint(str(uuid4()), variable_coeffs, lb=-total_sum + NUMERIC_STABLE_EPSILON)
    linconstr.canonicalize()
    linconstrs.append(linconstr)
    return linconstrs

def add_conflicts_to_model(m, objective_expr, conflicts, var_map):

    conflict_ind = 0
    for conflict in conflicts:

        # NOTE: Must assume for all relaxable constraints, including the decoupling constraints, they are marked as relaxable
        linconstrs = conflict_to_linconstr(conflict)
        inds = []
        linconstr_ind = 0
        for linconstr in linconstrs:
            # Initialize indicator variable
            ind = m.addVar(vtype=GRB.BINARY, name="conflict-ind-{}-{}".format(conflict_ind, linconstr_ind))
            inds.append(ind)

            # If ind == True, linconstr is satisfied
            coeff_var = []
            for var, coeff in linconstr.variable_coeffs.items():
                # Create variable for any local constraint relaxation
                if var not in var_map:
                    gp_var = m.addVar(lb=-MAX_NUMERIC_BOUND, ub=MAX_NUMERIC_BOUND, vtype=GRB.CONTINUOUS, name="{}".format(var))
                    var_map[var] = gp_var
                    # Add to objective_expr
                    # TODO: add linear cost too
                    constraint, boundtype = var
                    if boundtype == 'UB+' or boundtype == 'UB-':
                        objective_expr.add(gp_var, constraint.ub_lin_cost)
                    elif boundtype == 'LB+' or boundtype == 'LB-':
                        objective_expr.add(gp_var, constraint.lb_lin_cost)
                    else:
                        raise ValueError
                    m.addConstr(gp_var >= 0)
                coeff_var.append((float(coeff), var_map[var]))
            linexpr = gp.LinExpr(coeff_var)
            assert(linconstr.lb is None or linconstr.ub is None)
            # Add linconstr to model
            if linconstr.lb is not None:
                m.addConstr(linexpr >= linconstr.lb - (1-ind) * MAX_NUMERIC_BOUND, name="conflict-{}-{}".format(conflict_ind, linconstr_ind))
            if linconstr.ub is not None:
                m.addConstr(linexpr <= linconstr.ub + (1-ind) * MAX_NUMERIC_BOUND, name="conflict-{}-{}".format(conflict_ind, linconstr_ind))

            # Increment linconstr index
            linconstr_ind += 1

        # Make sure one linconstr is satisfied, i.e. SUM(inds) >= 1
        m.addConstr(gp.quicksum(inds) >= 1, name="conflict-{}".format(conflict_ind))

        # Increment conflict index
        conflict_ind += 1


if __name__ == '__main__':
    from dc_checking.temporal_network import TemporalNetwork, SimpleContingentTemporalConstraint, SimpleTemporalConstraint
    from dc_checking.dc_milp import DCCheckerMILP
    from dc_checking.dc_be import DCCheckerBE
    from compute_relaxation import *

    # Controllable
    # c1 = SimpleContingentTemporalConstraint('e1', 'e5', 15, 18.8554, 'c1')
    # Uncontrollable
    c1 = SimpleContingentTemporalConstraint('e1', 'e5', 0.6294, 18.8554, 'c1')
    c2 = SimpleTemporalConstraint('e1', 'e2', 1, 100, 'c2')
    c3 = SimpleTemporalConstraint('e2', 'e5', 0, 100, 'c3')
    c4 = SimpleTemporalConstraint('e2', 'e3', 1, 100, 'c4')
    c5 = SimpleTemporalConstraint('e3', 'e4', 1.5, 100, 'c5')
    c6 = SimpleTemporalConstraint('e1', 'e4', 1, 3.5, 'c6')
    network = TemporalNetwork([c1, c2, c3, c4, c5, c6])
    c1.annotation['lb_relaxable'] = True
    c1.annotation['lb_lin_cost'] = 100
    c1.annotation['ub_relaxable'] = True
    c1.annotation['ub_lin_cost'] = 100
    c2.annotation['lb_relaxable'] = False
    c2.annotation['lb_lin_cost'] = 100
    c2.annotation['ub_relaxable'] = False
    c2.annotation['ub_lin_cost'] = 100
    c3.annotation['lb_relaxable'] = True
    c3.annotation['lb_lin_cost'] = 100
    c3.annotation['ub_relaxable'] = True
    c3.annotation['ub_lin_cost'] = 100
    c6.annotation['lb_relaxable'] = True
    c6.annotation['lb_lin_cost'] = 100
    c6.annotation['ub_relaxable'] = True
    c6.annotation['ub_lin_cost'] = 100

    # DC Checker using Bucket Elimination
    checker = DCCheckerBE(network)
    controllable, conflict = checker.is_controllable(visualize=False, visualize_conflict=False)
    print(controllable, conflict)
    if not controllable:
        relaxation = compute_relaxation(conflict)
        if relaxation is not None:
            print(relaxation)
