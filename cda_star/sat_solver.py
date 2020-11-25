#!/usr/bin/env python

"""
SAT Solver implementation, using DPLL with unit propagation.
"""

from propositional_state_logic import *
from clauses import *

class SATSolver():
    def __init__(self, prob):
        self.prob = prob
        # Before we start, gather a comprehensive list of atom's (each of which will
        # be assigned a truth value). In our case, each atom represents an assignment
        # to a variable (propositional state logic).
        self.atoms_all = self.get_all_atoms()
        # Convert the already-entered expressions into CNF, (conjunctive) sets of (disjunctive) clauses
        self.cnf_gen = CNFGenerator()
        self.model_clauses = self.cnf_gen.convert_expressions_to_cnf(prob.get_all_constraints())


    def check_consistency(self, assignments):
        """ Constistency check! Given the given assignment,
        figures out whether all clauses are satisfiable, and returns a
        conflict if not.

        Input: assignments (a frozenset of Assignment objects)

        Output: A tuple (consistent, assignments, conflict), where consistent is True
                or False. If it's True, conflict is None, and assignments will be a frozenset of Assignment objects
                representing a satisfying assignment. Otherwise, if consistent is false, then assignments will be None
                and conflicts will be a frozenset of Assignment objects representing an extracted conflict.
        """
        # First, convert the assignments to clauses, and merge them with the model_clauses
        # clauses so that we give the SAT solver a full set.
        clauses = self.copy_clauses(self.model_clauses)
        clauses.extend(self.cnf_gen.convert_expressions_to_cnf(assignments))
        # Perform a round of unit propagation. This is where we can get
        # a nice conflict if it gets proven inconsistent (which unit propagation
        # is not guaranteed to do).
        clauses_up, assignments_up, conflict = self.unit_propagate(clauses, frozenset())
        if assignments_up is None:
            # Convert the set of all assigned literals just to positive assignments
            conflict_assignments = frozenset([a.atom for a in conflict if a.positive])
            return False, None, conflict_assignments
        # Unit propagation indicates it could be consistent. Use DPLL to do further search
        assignments_dpll = self.dpll(clauses_up, assignments=assignments_up)
        if assignments_dpll:
            assignments_out = frozenset([a.atom for a in assignments_dpll if a.positive])
            return True, assignments_out, None
        else:
            # It's inconsistent! Return the best conflict we can easily,
            # find, namely the original assignments
            return False, None, assignments


    def dpll(self, clauses, assignments=frozenset()):
        """ Implements the DPLL algorithm for checking satisfiability!

        In a nutshell, this algorithm works by searching over assignments
        to the literals. After each assignment is made, perform a round
        of unit propagation.

        Input: clauses (a list of Clause) objects,
               assignments (a frozenset of Literal objects that are currently assigned)

        Output:  assignments (a frozenset of Literal objects) if we've found a consistent
                assignment to every atom, or None if the problem is inconsistent."""

        # Perform an initial round of unit propagation. This will take care of
        # assigning anything that's a unit clause (for example, constraints like x = 1).
        # Also, since CDA* only calls dpll on getting a full assignment to decision variables,
        # we can be sure those will get assigned by unit propagation and we won't need to
        #print "********************"
        clauses, assignments, conflict = self.unit_propagate(clauses, assignments, extract_conflict=False)
        #print assignments, clauses
        #import IPython; IPython.embed()

        if assignments is None:
            return None # Provably infeasible!
        else:
            # Choose an unassigned atom (if there are any left)
            atom = self.choose_unassigned_atom(assignments)
            if atom == None:
                # Everything is assigned! We win!
                return assignments
            else:
                for truthfulness in [False, True]:
                    literal = Literal(atom, truthfulness)
                    assignments_r = assignments | frozenset([literal])
                    assignments_r = self.dpll(clauses, assignments=assignments_r)
                    if assignments_r:
                        return assignments_r
                # If we get here, we've failed at recursing assigning this atom
                # both True and False. This means we've proven failure!
                return None


    def unit_propagate(self, clauses, assignments, extract_conflict=True):
        """ Implements the unit propagation algorithm.

        Takes as input a list of Clause objects representing the constraints (not modified),
        as well as a list of assignments so far. Returns a tuple: (clauses, assignments, conflicts).
        If the formula is proved inconsistent, then conflicts is None. Otherwise, it will be a list
        of assignments which form a conflict.

        Input: clauses (a list of Clause objects), assignments (a frozenset of Literals),
               extract_conflict: True/False, for if we want to trace conflict supports upon
               discovering an inconsistency.

        Output: clauses (a list of Clause objects), assignments (a frozenset of Literals), and
                conflict (a frozenset of literals reprsenting a conflict)
        """
        # Make a copy
        assignments = set(assignments)
        clauses = self.copy_clauses(clauses)
        # Supports for literal assignments
        support_trace = {}
        # Do initial removing
        clauses = self.remove_clauses_satisfied_by_assignment(clauses, assignments)

        for clause in clauses:
            clause.remove_false_literals(assignments)
        # Search for unit clauses
        # IMPORTANT! Be sure any unit clauses are assigned first...
        # otherwise tracing doesn't work. The following algorithm guarantees this!

        # Set up a Q which will contain clauses that need further processing.
        # Initially set it to the list of unit clauses, since we can guarantee
        # that assignments will be made there.
        Q = [c for c in clauses if c.length() == 1]
        while len(Q) > 0:
            clause = Q.pop(0)
            # Filter out any false literals
            clause.remove_false_literals(assignments)
            if clause.length() == 1:
                # Great! We can make a new assignment!
                literal = list(clause.literals)[0]
                # Sanity check!
                if literal in assignments or literal in support_trace:
                    # Detect this! It can seriously mess up conflict extraction and cause there to be cycles.
                    raise Exception("Found a bug in unit propagation: assigning a literal that's already assigned!")
                # Assign it and record support.
                assignments.add(literal)
                support_trace[literal] = clause
                # Remove clauses that are now guaranteed to be true
                clauses = self.remove_clauses_satisfied_by_assignment(clauses, assignments)
                # Remove any clauses waiting in the Q that are now true (no longer need to process)
                Q = [c for c in Q if not literal in c.literals]
                # Find all clauses that mention the negation of this literal, and
                # add them to the Q (they could become unit clauses)
                ln = literal.negate()
                Q.extend([c for c in clauses if ln in c.literals])

            elif clause.length() == 0:
                conflict = self.get_conflict(clause, support_trace) if extract_conflict else None
                return None, None, conflict

        # We get here if there are no more unit clauses. Done with unit propagation.
        # The problem is possibly consistent - we haven't proven it inconsistent.
        return clauses, frozenset(assignments), None


    def get_conflict(self, conflict_clause, support_trace):
        """ Extract conflicts by tracing back supports. """
        return self.trace_supports(None, conflict_clause, support_trace)


    def trace_supports(self, literal, conflict_clause, support_trace):
        """ Traces support for a now-empty clause to help find a conflict """
        supports = []
        # print("Support Trace: ", support_trace)
        # print("{} : {} : {}".format(conflict_clause.index, conflict_clause.literals_original, literal))
        if len(conflict_clause.literals_original) == 1:
            l = list(conflict_clause.literals_original)[0]
            if isinstance(l.atom, Assignment) and l.atom.var.decision_variable and l.positive:
                return [l]
            else:
                return []
        else:
            for l in conflict_clause.literals_original:
                ln = l.negate()
                if l != literal and ln in support_trace:
                    supports.extend(self.trace_supports(ln, support_trace[ln], support_trace))
            return supports


    def remove_clauses_satisfied_by_assignment(self, clauses, assignments):
        """ Removes from clauses, any clause that is already satisfied
        by any of the assignments (a list) """
        return [clause for clause in clauses if not clause.is_satisfied_by_assignments(assignments)]

    def get_all_atoms(self):
        """ Helper function to retrieve all atoms."""
        atoms = []
        for var in self.prob.variables:
            atoms.extend(var.assignments.values())
        return set(atoms)

    def choose_unassigned_atom(self, assignments):
        """ Helper function to return an unassigned literal, or None if they're all assigned """
        atoms_unassigned = list(self.atoms_all - set(literal.atom for literal in assignments))
        if len(atoms_unassigned) == 0:
            return None
        else:
            return atoms_unassigned[0]

    def copy_clauses(self, clauses):
        return [clause.copy() for clause in clauses]
