import IPython
from nose.tools import assert_equal, ok_
from propositional_state_logic import *
from sat_solver import *

def test_ok():
    """ If execution gets to this point, print out a happy message """
    try:
        from IPython.display import display_html
        display_html("""<div class="alert alert-success">
        <strong>Tests passed!!</strong>
        </div>""", raw=True)
    except:
        print("Tests passed!!")


"""
Model checking code
"""
def check_polycell_problem(prob):
    check_no_observations(prob)
    check_and_gate(prob, 'A1', inputs=['A', 'C'], output='X')
    check_and_gate(prob, 'A2', inputs=['B', 'D'], output='Y')
    check_and_gate(prob, 'A3', inputs=['C', 'E'], output='Z')
    check_xor_gate(prob, 'X1', inputs=['X', 'Y'], output='F')
    check_xor_gate(prob, 'X2', inputs=['Y', 'Z'], output='G')

def check_no_observations(prob):
    checks = []
    print("Checking mode and observation variables...")
    for var in ['A', 'B', 'C', 'D', 'E', 'F', 'X', 'Y', 'Z']:
        checks.extend([([(var, 'True')], True), ([(var, 'False')], True)])
    for var in ['A1', 'A2', 'A3', 'X1', 'X2']:
        checks.extend([([(var, 'G')], True), ([(var, 'U')], True)])
    result, entry = check_truth_table(prob, checks)
    ok_(result, msg="Something wrong with constraints: {}".format(get_explanation(entry)))


def check_and_gate(prob, name, inputs, output):
    print("Checking {}...".format(name))
    in1, in2 = inputs
    checks = [## Good mode!
              # Both inputs true
              ([(name, 'G'), (in1, 'True'), (in2, 'True'), (output, 'True')], True),
              ([(name, 'G'), (in1, 'True'), (in2, 'True'), (output, 'False')], False),
              # First input false
              ([(name, 'G'), (in1, 'False'), (in2, 'True'), (output, 'True')], False),
              ([(name, 'G'), (in1, 'False'), (in2, 'True'), (output, 'False')], True),
              # Second input false
              ([(name, 'G'), (in1, 'True'), (in2, 'False'), (output, 'True')], False),
              ([(name, 'G'), (in1, 'True'), (in2, 'False'), (output, 'False')], True),
              # Both inputs false
              ([(name, 'G'), (in1, 'False'), (in2, 'False'), (output, 'True')], False),
              ([(name, 'G'), (in1, 'False'), (in2, 'False'), (output, 'False')], True),
              ## Bad mode!
              # Both inputs true
              ([(name, 'U'), (in1, 'True'), (in2, 'True'), (output, 'True')], True),
              ([(name, 'U'), (in1, 'True'), (in2, 'True'), (output, 'False')], True),
              # First input false
              ([(name, 'U'), (in1, 'False'), (in2, 'True'), (output, 'True')], True),
              ([(name, 'U'), (in1, 'False'), (in2, 'True'), (output, 'False')], True),
              # Second input false
              ([(name, 'U'), (in1, 'True'), (in2, 'False'), (output, 'True')], True),
              ([(name, 'U'), (in1, 'True'), (in2, 'False'), (output, 'False')], True),
              # Both inputs false
              ([(name, 'U'), (in1, 'False'), (in2, 'False'), (output, 'True')], True),
              ([(name, 'U'), (in1, 'False'), (in2, 'False'), (output, 'False')], True),
              ]
    result, entry = check_truth_table(prob, checks)
    ok_(result, msg="And gate {} doesn't seem to work: {}".format(name, get_explanation(entry)))


def check_xor_gate(prob, name, inputs, output):
    print("Checking {}...".format(name))
    in1, in2 = inputs
    checks = [## Good mode!
              # Both inputs true
              ([(name, 'G'), (in1, 'True'), (in2, 'True'), (output, 'True')], False),
              ([(name, 'G'), (in1, 'True'), (in2, 'True'), (output, 'False')], True),
              # First input false
              ([(name, 'G'), (in1, 'False'), (in2, 'True'), (output, 'True')], True),
              ([(name, 'G'), (in1, 'False'), (in2, 'True'), (output, 'False')], False),
              # Second input false
              ([(name, 'G'), (in1, 'True'), (in2, 'False'), (output, 'True')], True),
              ([(name, 'G'), (in1, 'True'), (in2, 'False'), (output, 'False')], False),
              # Both inputs false
              ([(name, 'G'), (in1, 'False'), (in2, 'False'), (output, 'True')], False),
              ([(name, 'G'), (in1, 'False'), (in2, 'False'), (output, 'False')], True),
              ## Bad mode!
              # Both inputs true
              ([(name, 'U'), (in1, 'True'), (in2, 'True'), (output, 'True')], True),
              ([(name, 'U'), (in1, 'True'), (in2, 'True'), (output, 'False')], True),
              # First input false
              ([(name, 'U'), (in1, 'False'), (in2, 'True'), (output, 'True')], True),
              ([(name, 'U'), (in1, 'False'), (in2, 'True'), (output, 'False')], True),
              # Second input false
              ([(name, 'U'), (in1, 'True'), (in2, 'False'), (output, 'True')], True),
              ([(name, 'U'), (in1, 'True'), (in2, 'False'), (output, 'False')], True),
              # Both inputs false
              ([(name, 'U'), (in1, 'False'), (in2, 'False'), (output, 'True')], True),
              ([(name, 'U'), (in1, 'False'), (in2, 'False'), (output, 'False')], True),
              ]
    result, entry = check_truth_table(prob, checks)
    ok_(result, msg="Xor gate {} doesn't seem to work: {}".format(name, get_explanation(entry)))


def get_explanation(entry):
    if entry != None:
        var_assignments, expected_result = entry
        return "Assigning {{{}}} {} satisfiable!".format(', '.join('{} = {}'.format(var, val) for (var, val) in var_assignments), "is" if not(expected_result) else "isn't")
    else:
        return ""

def check_truth_table(prob, truth_table):
    sat = SATSolver(prob)
    for entry in truth_table:
        var_assignments, expected_result = entry # Unpack
        assignment = frozenset([prob.name_to_var[var_name].get_assignment(value) for (var_name, value) in var_assignments])
        consistent, full_assignment, conflicts = sat.check_consistency(assignment)
        if consistent != expected_result:
            return False, entry
    # All checks pass!
    return True, None


"""
Probability checking code
"""
def check_estimate_probability(fn):
    """ Make a sample problem to test with """
    p = Problem()
    x = p.add_variable('x', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    y = p.add_variable('y', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    z = p.add_variable('z', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    x.set_probabilities({
        '1': 0.8,
        '2': 0.15,
        '3': 0.05
    })
    y.set_probabilities({
        '1': 0.9,
        '2': 0.08,
        '3': 0.02
    })
    z.set_probabilities({
        '1': 0.7,
        '2': 0.2,
        '3': 0.1
    })
    assert_equal(fn(frozenset([]), p.get_decision_variables()), 0.8*0.9*0.7)
    assert_equal(fn(frozenset([x.get_assignment('2')]), p.get_decision_variables()), 0.15*0.9*0.7)
    assert_equal(fn(frozenset([x.get_assignment('2'), y.get_assignment('3')]), p.get_decision_variables()), 0.15*0.02*0.7)
    assert_equal(fn(frozenset([x.get_assignment('2'), y.get_assignment('3'), z.get_assignment('1')]), p.get_decision_variables()), 0.15*0.02*0.7)


"""
Conflict checking
"""
def check_manifests_conflict(fn):
    p = Problem()
    x = p.add_variable('x', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    y = p.add_variable('y', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    z = p.add_variable('z', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    assert_equal(fn(frozenset([x.get_assignment('1')]), frozenset([x.get_assignment('1')])), True)
    assert_equal(fn(frozenset([x.get_assignment('1'), y.get_assignment('2')]), frozenset([x.get_assignment('1')])), True)
    assert_equal(fn(frozenset([x.get_assignment('1')]), frozenset([x.get_assignment('1'), y.get_assignment('2')])), False)
    assert_equal(fn(frozenset([x.get_assignment('1')]), frozenset([])), True)


def check_resolves_conflict(fn):
    p = Problem()
    x = p.add_variable('x', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    y = p.add_variable('y', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    z = p.add_variable('z', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    # Not resolving conflicts
    assert_equal(fn(frozenset([x.get_assignment('1')]), frozenset([x.get_assignment('1')])), False)
    assert_equal(fn(frozenset([x.get_assignment('1'), y.get_assignment('2')]), frozenset([x.get_assignment('1')])), False)
    assert_equal(fn(frozenset([x.get_assignment('1')]), frozenset([x.get_assignment('1'), y.get_assignment('2')])), False)
    assert_equal(fn(frozenset([x.get_assignment('1')]), frozenset([z.get_assignment('1')])), False)
    assert_equal(fn(frozenset([x.get_assignment('1')]), frozenset([])), False)
    # Resolving conflict
    assert_equal(fn(frozenset([x.get_assignment('2')]), frozenset([x.get_assignment('1')])), True)
    assert_equal(fn(frozenset([x.get_assignment('2'), y.get_assignment('2')]), frozenset([x.get_assignment('1')])), True)
    assert_equal(fn(frozenset([x.get_assignment('2')]), frozenset([x.get_assignment('1'), y.get_assignment('2')])), True)

"""
Check Splitting
"""

def check_choose_variable_to_split_on(fn):
    p = Problem()
    x = p.add_variable('x', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    y = p.add_variable('y', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    z = p.add_variable('z', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    ok_(fn(frozenset([]), p.get_decision_variables()) in set([x, y, z]))
    ok_(fn(frozenset([x.get_assignment('1')]), p.get_decision_variables()) in set([y, z]))
    ok_(fn(frozenset([y.get_assignment('1')]), p.get_decision_variables()) in set([x, z]))
    ok_(fn(frozenset([z.get_assignment('1')]), p.get_decision_variables()) in set([x, y]))
    ok_(fn(frozenset([x.get_assignment('1'), y.get_assignment('2')]), p.get_decision_variables()) == z)


def check_split_on_variable(fn):
    p = Problem()
    x = p.add_variable('x', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    y = p.add_variable('y', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    z = p.add_variable('z', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    assert_equal(set(fn(frozenset([]), x)),
        set([
            frozenset([x.get_assignment('1')]),
            frozenset([x.get_assignment('2')]),
            frozenset([x.get_assignment('3')]),
        ]))
    assert_equal(set(fn(frozenset([y.get_assignment('2')]), x)),
        set([
            frozenset([y.get_assignment('2'), x.get_assignment('1')]),
            frozenset([y.get_assignment('2'), x.get_assignment('2')]),
            frozenset([y.get_assignment('2'), x.get_assignment('3')]),
        ]))


def check_split_on_conflict(fn):
    p = Problem()
    x = p.add_variable('x', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    y = p.add_variable('y', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)
    z = p.add_variable('z', type='finite_domain', domain=['1', '2', '3'], decision_variable=True)

    # The universal conflict should yield no neighbors!
    assert_equal(set(fn(frozenset([]), frozenset([]))),
        set([])
    )
    assert_equal(set(fn(frozenset([]), frozenset([x.get_assignment('1')]))),
        set([
            frozenset([x.get_assignment('2')]),
            frozenset([x.get_assignment('3')]),
        ])
    )
    assert_equal(set(fn(frozenset([]), frozenset([x.get_assignment('1'), y.get_assignment('1')]))),
        set([
            frozenset([x.get_assignment('2')]),
            frozenset([x.get_assignment('3')]),
            frozenset([y.get_assignment('2')]),
            frozenset([y.get_assignment('3')]),
        ])
    )
    assert_equal(set(fn(frozenset([z.get_assignment('1')]), frozenset([x.get_assignment('1'), y.get_assignment('1')]))),
        set([
            frozenset([z.get_assignment('1'), x.get_assignment('2')]),
            frozenset([z.get_assignment('1'), x.get_assignment('3')]),
            frozenset([z.get_assignment('1'), y.get_assignment('2')]),
            frozenset([z.get_assignment('1'), y.get_assignment('3')]),
        ])
    )


"""
Various other utility functions
"""
def display_constraints(prob):
    print("Constraints:")
    try:
        from IPython.display import display, Latex
        for c in prob.constraints:
            display(Latex(c._repr_latex_()))
    except:
        for c in prob.constraints:
            print(c)
