#!/usr/bin/env python
# -*- coding: utf-8 -*-

import itertools
from propositional_state_logic import *

class Literal():
    def __init__(self, atom, positive):
        self.atom = atom
        self.positive = positive

    def __str__(self):
        if self.positive:
            return str(self.atom)
        else:
            return "¬{}".format(self.atom)

    def __hash__(self):
        return hash((self.atom, self.positive))

    def __eq__(self, other):
        if other == None:
            return False
        return self.atom == other.atom and self.positive == other.positive

    def is_complement(self, other):
        """ Returns True if the other literal is the complicated (i.e., negated)
        version of this one. """
        return (self.atom == other.atom) and (self.positive != other.positive)

    def negate(self):
        """ Returns the complement literal """
        return Literal(self.atom, not(self.positive))


    __repr__ = __str__


class Clause():
    def __init__(self, literals, index=0):
        # Store the literals, and and also an original unmodified copy, useful for tracing
        # supports later during unit propagation
        self.literals = set(literals)
        self.literals_original = set(literals)
        self.index = index

    def __str__(self):
        return "<Clause {}: {}>".format(self.index, str(self.literals))
    __repr__ = __str__

    def is_satisfied_by_assignments(self, assignments):
        """ Returns true if this clause is satisfied by any of the given assignments,
        which is a list of literals. False otherwise. """
        return any(assignment in self.literals for assignment in assignments)

    def remove_false_literals(self, assignments):
        """ Removes any literals from this clause that are guaranteed to be false
        under assignments, which is a list of literals.

        Leaves literals_original unmodified."""
        for assignment in assignments:
            self.literals = set(c for c in self.literals if not assignment.is_complement(c))

    def length(self):
        return len(self.literals)

    def copy(self):
        return Clause(self.literals, index=self.index)


class CNFGenerator():
    """ Class to help convert expressions to conjunctive normal form (CNF) """
    def __init__(self):
        pass

    def convert_expressions_to_cnf(self, exps):
        clauses = []
        for exp in exps:
            clauses.extend(self.convert_expression_cnf(exp))
        for (i, clause) in enumerate(clauses):
            clause.index = i
        return clauses

    def convert_expression_cnf(self, exp):
        exp = self.compile_away_operators(exp) # Compile away certain operators
        return [Clause(c) for c in self.cnf_recursive_helper(exp)]

    def simplify(self, clauses):
        # Do some basic simplifications on clauses!
        clauses_simplified = []
        # If there are any clauses that contain both X and not(X), they are
        # definitely true, so we can remove those clauses.
        for clause in clauses:
            definitely_true  = False
            for (literal_i, literal_j) in itertools.combinations(clause, 2):
                if literal_i.atom == literal_j.atom and literal_i.positive != literal_j.positive:
                    # Found a clause that is definitely true!
                    definitely_true = True
                    break
            if not definitely_true:
                clauses_simplified.append(clause)

        clauses = clauses_simplified[:]
        clauses_simplified = []
        # Also, remove any duplicate elements
        for clause in clauses:
            clauses_simplified.append(list(set(clause)))

        return clauses_simplified



    def cnf_recursive_helper(self, exp):
        """ This algorithm is based on:
        https://www.cs.jhu.edu/~jason/tutorials/convert-to-CNF.html """
        if isinstance(exp, Assignment):
            return [[Literal(exp, True)]]

        elif isinstance(exp, Variable):
            return [[Literal(exp, True)]]

        elif isinstance(exp, Negation):
            obj = exp.obj
            if isinstance(obj, Variable):
                return [[Literal(obj, False)]]
            elif isinstance(obj, Assignment):
                return [[Literal(obj, False)]]
            elif isinstance(obj, Negation):
                return self.cnf_recursive_helper(obj.obj)
            elif isinstance(obj, Conjunction):
                return self.cnf_recursive_helper(Disjunction([Negation(c) for c in obj.conjuncts]))
            elif isinstance(obj, Disjunction):
                return self.cnf_recursive_helper(Conjunction([Negation(d) for d in obj.disjuncts]))

        elif isinstance(exp, Conjunction):
            clauses = []
            for conjunct in exp.conjuncts:
                clauses.extend(self.cnf_recursive_helper(conjunct))
            return clauses

        elif isinstance(exp, Disjunction):
            clauses_list = [self.cnf_recursive_helper(d) for d in exp.disjuncts]
            clauses = []
            for d_cross_product in itertools.product(*clauses_list):
                disjuncts = []
                for d in d_cross_product:
                    disjuncts.extend(d)
                clauses.append(disjuncts)
            return self.simplify(clauses)


    def compile_away_operators(self, expression):
        """ Helper function to compile away certain operators that can be defined
        in terms of lower-level operators. These include => (implication),
        <=> (equivalence), and ^ (xor) """

        if isinstance(expression, Assignment):
            return expression

        elif isinstance(expression, Negation):
            expression.obj = self.compile_away_operators(expression.obj)
            return expression

        elif isinstance(expression, Conjunction):
            expression.conjuncts = [self.compile_away_operators(c) for c in expression.conjuncts]
            return expression

        elif isinstance(expression, Disjunction):
            expression.disjuncts = [self.compile_away_operators(d) for d in expression.disjuncts]
            return expression

        elif isinstance(expression, Xor):
            return self.compile_away_operators(self.convert_xor(expression))

        elif isinstance(expression, Implication):
            return self.compile_away_operators(self.convert_implication(expression))

        elif isinstance(expression, Equivalence):
            return self.compile_away_operators(self.convert_equivalence(expression))

        else:
            raise Exception("Unknown type for compiling away operators: {}".format(expression.__class__))


    def convert_implication(self, imp):
        return Disjunction([Negation(imp.antecedent), imp.consequent])

    def convert_equivalence(self, equiv):
        return Disjunction([Conjunction([equiv.antecedent, equiv.consequent]), Conjunction([Negation(equiv.antecedent), Negation(equiv.consequent)])])

    def convert_xor(self, exp):
        cnjs = []
        for xi in exp.disjuncts:
            cnj = []
            for ci in exp.disjuncts:
                if xi == ci:
                    cnj.append(Negation(ci))
                else:
                    cnj.append(ci)
            cnjs.append(Conjunction(cnj))
        return Disjunction(cnjs)
