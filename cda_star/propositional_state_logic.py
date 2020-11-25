#!/usr/bin/env python
# -*- coding: utf-8 -*-

# Parsing test
import itertools
import pyparsing
pyparsing.ParseElementEnhance.enablePackrat() # Without this it's exceptionally slow...


class Expression():
    def _repr_latex_(self):
        return "$${}$$".format(self.to_latex())
    def to_latex(self):
        return str(self)
    def __repr__(self):
        return str(self)


class Term(Expression):
    # Not sure yet if it's a variable or a domain value - will be determined
    # in a post-procesing stage
    def __init__(self, name, ):
        self.name = str(name)

    def __str__(self):
        return self.name


class Variable(Expression):
    def __init__(self, name, domain=['True', 'False'], type='binary', decision_variable=False):
        self.name = str(name)
        self.domain = frozenset(domain)
        self.type = type
        self.decision_variable = decision_variable
        self.assignments = {}
        # Initialize assignments
        for di in self.domain:
            self.assignments[di] = Assignment((self, di))

    def get_assignment(self, di):
        if not di in self.domain:
            raise Exception("Value '{}' is not in domain of variable '{}'!".format(di, self.name))
        else:
            return self.assignments[di]

    def set_probabilities(self, prob_desc):
        # Do some sanity checking
        di_mentioned = set(prob_desc.keys())
        if len(di_mentioned - self.domain) > 0:
            raise Exception("You tried to set probabilities for variable {}'s invalid domain values {}!".format(self.name, ', '.join(di_mentioned - self.domain)))
        elif len(self.domain - di_mentioned) > 0:
            raise Exception("You forgot to assign probabilities for variable {}'s domain value(s) for {}!".format(self.name, ', '.join(self.domain - di_mentioned)))
        # Also require them to sum to 1.
        if abs(sum(prob_desc.values())-1.0) > 0.000001:
            raise Exception("Probabilities you specified sum to {}, not 1.0!".format(sum(prob_desc.values())))
        # Good to go
        for (di, pi) in prob_desc.items():
            self.get_assignment(di).prob = pi
        return True

    def __str__(self):
        return self.name


class Negation(Expression):
    def __init__(self, obj):
        self.obj = obj

    def __str__(self):
        return '¬{}'.format(parenify(self, self.obj))

    def to_latex(self):
        return '\\neg {}'.format(parenify(self, self.obj, recurse_str=to_latex))


class Assignment(Expression):
    def __init__(self, objs):
        self.objs = objs
        if len(self.objs) != 2:
            raise Exception('Invalid assignment! Can only have a variable (left) and value (right)') # TODO
        self.var = self.objs[0]
        self.val = self.objs[1]
        self.prob = None

    def __str__(self):
        #return '({} = {})'.format(self.var, self.val)
        if self.var.type == 'finite_domain':
            return '({} = {})'.format(self.var, self.val)
        else:
            # Special case! Pretty print assignments to binary vars
            if self.val == 'True':
                return '{}'.format(self.var)
            else:
                return '¬{}'.format(self.var)

    def to_latex(self):
        #return '({} = {})'.format(self.var, self.val)
        if self.var.type == 'finite_domain':
            return '({} = {})'.format(self.var, self.val)
        else:
            # Special case! Pretty print assignments to binary vars
            if self.val == 'True':
                return '{}'.format(self.var)
            else:
                return '\\neg {}'.format(self.var)

class Conjunction(Expression):
    def __init__(self, conjuncts):
        self.conjuncts = conjuncts

    def __str__(self):
        return ' ∧ '.join(parenify(self, c) for c in self.conjuncts)

    def to_latex(self):
        return ' \\wedge '.join(parenify(self, c, recurse_str=to_latex) for c in self.conjuncts)

class Disjunction(Expression):
    def __init__(self, disjuncts):
        self.disjuncts = disjuncts

    def __str__(self):
        return ' ∨ '.join(parenify(self, d) for d in self.disjuncts)

    def to_latex(self):
        return ' \\vee '.join(parenify(self, d, recurse_str=to_latex) for d in self.disjuncts)


class Xor(Expression):
    def __init__(self, disjuncts):
        self.disjuncts = disjuncts

    def __str__(self):
        return ' ⊕ '.join(parenify(self, d) for d in self.disjuncts)

    def to_latex(self):
        return ' \\oplus '.join(parenify(self, d, recurse_str=to_latex) for d in self.disjuncts)


class Implication(Expression):
    def __init__(self, objs):
        self.objs = objs
        if len(self.objs) != 2:
            raise Exception('Invalid implication! Please use parenthesis to clarify') # TODO
        self.antecedent = self.objs[0]
        self.consequent = self.objs[1]

    def __str__(self):
        return '{} ⇒ {}'.format(parenify(self, self.antecedent), parenify(self, self.consequent))

    def to_latex(self):
        return '{} \\Rightarrow {}'.format(parenify(self, self.antecedent, recurse_str=to_latex), parenify(self, self.consequent, recurse_str=to_latex))

class Equivalence(Expression):
    def __init__(self, objs):
        self.objs = objs
        if len(self.objs) != 2:
            raise Exception('Invalid equivalence! Please use parenthesis to clarify') # TODO
        self.antecedent = self.objs[0]
        self.consequent = self.objs[1]

    def __str__(self):
        return '{} ⇔ {}'.format(parenify(self, self.antecedent), parenify(self, self.consequent))

    def to_latex(self):
        return '{} \\Leftrightarrow {}'.format(parenify(self, self.antecedent, recurse_str=to_latex), parenify(self, self.consequent, recurse_str=to_latex))


def to_latex(obj):
    return obj.to_latex()


operator_precedence = {
    Term: 0,
    Variable: 0,
    Assignment: 1,
    Negation: 2,
    Conjunction: 3,
    Disjunction: 4,
    Xor: 5,
    Implication: 6,
    Equivalence: 7
}

def parenify(outer, inner, recurse_str=str):
    # Inner is an object nested inside outer. Add parenthesis if necessary!
    add_parens = operator_precedence[outer.__class__] < operator_precedence[inner.__class__]
    return "({})".format(recurse_str(inner)) if add_parens else recurse_str(inner)


def get_formula_parser():
    def make_term_from_pargs(pargs):
        return Term(pargs[0])

    def make_assignment_from_pargs(pargs):
        return Assignment(pargs[0][0::2])

    def make_negation_from_pargs(pargs):
        return Negation(pargs[0][1])

    def make_conjunction_from_pargs(pargs):
        return Conjunction(pargs[0][0::2])

    def make_disjunction_from_pargs(pargs):
        return Disjunction(pargs[0][0::2])

    def make_xor_from_pargs(pargs):
        return Xor(pargs[0][0::2])

    def make_implication_from_pargs(pargs):
        return Implication(pargs[0][0::2])

    def make_equivalence_from_pargs(pargs):
        return Equivalence(pargs[0][0::2])

    term = pyparsing.Word(pyparsing.alphanums + "_")
    term.setParseAction(make_term_from_pargs)
    return pyparsing.infixNotation(term,
            [
            ('=', 2, pyparsing.opAssoc.LEFT, make_assignment_from_pargs),
            ('~', 1, pyparsing.opAssoc.RIGHT, make_negation_from_pargs),
            ('&', 2, pyparsing.opAssoc.LEFT, make_conjunction_from_pargs),
            ('|', 2, pyparsing.opAssoc.LEFT, make_disjunction_from_pargs),
            ('^', 2, pyparsing.opAssoc.LEFT, make_xor_from_pargs),
            ('=>', 2, pyparsing.opAssoc.LEFT, make_implication_from_pargs),
            ('<=>', 2, pyparsing.opAssoc.LEFT, make_equivalence_from_pargs),
            ])


class Problem():
    def __init__(self):
        # Useful datastructures
        self.variables = []
        self.constraints = []
        self.name_to_var = {}
        self.probs = {}
        # Set up the parser
        self.expr_parser = get_formula_parser()

    def copy(self):
        """ Returns a copy of this problem, but over the same variables.
        Useful for having multiple problems, but each with different constraints. """
        prob_new = Problem()
        prob_new.variables = self.variables[:]
        prob_new.constraints = self.constraints[:]
        prob_new.name_to_var = self.name_to_var.copy()
        prob_new.probs = self.probs.copy()
        return prob_new

    def clear_constraints(self):
        """ Helper method to clear any entered constraints """
        self.constraints = []

    def parse_expression(self, expression_string):
        # Use pyparsing to do the initial parsing
        expr = self.expr_parser.parseString(expression_string, parseAll=True)[0]
        # Convert assignments and terms through a post-processing stage
        return self.parse_post_process(expr)

    def parse_post_process(self, expression):
        """ Performs post processing to type check assignments and variables """
        if isinstance(expression, Term):
            # If execution gets here, we've found an empty term outside of an assignment.
            # This is only okay if it's a binary variable, and will elaborate it to
            # the corresponding assignment.
            if not expression.name in self.name_to_var:
                raise Exception("Unknown variable: '{}'. Please use the 'add_variable' function first.".format(expression.name))
            var = self.name_to_var[expression.name]
            if var.type != 'binary':
                raise Exception("Variable '{}' was declared as finite_domain (not binary), so you can only use it in assignments, not alone".format(var.name))
            # Good! Passes checks
            return var.get_assignment("True")

        elif isinstance(expression, Assignment):
            # The first must be a finite_domain variable, the second a value in its domain
            if not isinstance(expression.var, Term) or not isinstance(expression.val, Term):
                raise Exception("You're using '=' incorrectly; you can only use it in the form of variable=value!")

            if not expression.var.name in self.name_to_var:
                raise Exception("Unknown variable: '{}'. Please use the 'add_variable' function first.".format(expression.var.name))
            var = self.name_to_var[expression.var.name]
            # Make sure it's in the domain...
            return var.get_assignment(expression.val.name)

        elif isinstance(expression, Negation):
            expression.obj = self.parse_post_process(expression.obj)
            return expression

        elif isinstance(expression, Conjunction):
            expression.conjuncts = [self.parse_post_process(c) for c in expression.conjuncts]
            return expression

        elif isinstance(expression, Disjunction):
            expression.disjuncts = [self.parse_post_process(d) for d in expression.disjuncts]
            return expression

        elif isinstance(expression, Xor):
            expression.disjuncts = [self.parse_post_process(x) for x in expression.disjuncts]
            return expression

        elif isinstance(expression, Implication) or isinstance(expression, Equivalence):
            expression.antecedent = self.parse_post_process(expression.antecedent)
            expression.consequent = self.parse_post_process(expression.consequent)
            return expression

        else:
            raise Exception("Unknown parsed type: {}".format(expression.__class__))




    def add_variable(self, name, type='binary', domain=None, decision_variable=False):
        # Do some validation
        if not type in ['binary', 'finite_domain']:
            raise Exception("Variable's 'type' must be either 'binary' or 'finite_domain'")
        if name in self.name_to_var:
            raise Exception("Multiple variables with the name '{}', please change your names!".format(name))

        if type == 'binary':
            if domain is not None:
                raise Exception("Don't specify domains for binary variables, it's automatically ['True', 'False']")
            domain = ['True', 'False']
        else:
            if domain is None or len(domain) == 0:
                raise Exception("Variable domains must not be empty, unless you want there to be no solutions!")

        if not all(isinstance(di, str) for di in domain):
            raise Exception("All domain values must be specified as string")
        # Create the variable!
        var = Variable(name, domain=domain, type=type, decision_variable=decision_variable)
        self.variables.append(var)
        self.name_to_var[name] = var
        return var

    def generate_variable_constraints(self):
        constraints = []
        for var in self.variables:
            constraints.append(Disjunction([var.get_assignment(val) for val in var.domain]))
            for (a1, a2) in itertools.combinations([var.get_assignment(val) for val in var.domain], 2):
                constraints.append(Negation(Conjunction([a1, a2])))
        return constraints

    def get_all_constraints(self):
        cs = []
        cs.extend(self.generate_variable_constraints())
        cs.extend(self.constraints)
        return cs


    def add_constraint(self, expression_string):
        m = self.parse_expression(expression_string)
        self.constraints.append(m)


    def sanity_check(self):
        """ Do some error checking that may save some debugging time! """
        self.check_probabilities()
        self.check_no_assigned_decision_variables()

    def check_probabilities(self):
        # Check that all necessary probabilty distributions are defined
        for var in self.variables:
            if var.decision_variable:
                if list(var.assignments.values())[0].prob == None:
                    raise Exception("Variable '{}' is a decision variable, so you need to specify its probability distribution!".format(var.name))
        return True

    def check_no_assigned_decision_variables(self):
        for exp in self.constraints:
            if isinstance(exp, Assignment):
                if exp.var.decision_variable:
                    raise Exception("You shouldn't assign decision variables like {} in your constraints!".format(exp.var.name))


    def get_variable(self, name):
        return self.name_to_var(name)


    def get_decision_variables(self):
        return frozenset([var for var in self.variables if var.decision_variable])
