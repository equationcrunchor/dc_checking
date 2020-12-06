from bcdr import *
import copy

def modify_problem(original_problem, new_constraints, new_temporal_constraints):
    new_prob = copy.deepcopy(original_problem)
    for constraint in new_constraints:
        new_prob.add_constraint(constraint)
    for new_constraint in new_temporal_constraints:
        new_prob.add_temporal_constraint(new_constraint)
    return new_prob

# example
constraints = [
    TPNConstraint('leave_work', 'arrive_home', None, 0, 180, 'c1'),
    TPNConstraint('leave_work', 'chin_rest', 'restaurant=chinese', 30, 120, 'c2'),
    TPNConstraint('leave_work', 'kor_rest', 'restaurant=korean', 10, 120, 'c3'),
    TPNConstraint('leave_work', 'g_mov_start', None, 40, 45, 'c4'),
    TPNConstraint('leave_work', 'b_mov_start', None, 60, 65, 'c5'),
    TPNConstraint('chin_rest', 'g_mov_start', 'movie=good', 30, 60, 'c6'),
    TPNConstraint('chin_rest', 'b_mov_start', 'movie=bad', 30, 60, 'c7'),
    TPNConstraint('kor_rest', 'g_mov_start', 'movie=good', 30, 60, 'c8'),
    TPNConstraint('kor_rest', 'b_mov_start', 'movie=bad', 30, 60, 'c9'),
    TPNConstraint('g_mov_start', 'arrive_home', None, 90, 120, 'c10'),
    TPNConstraint('b_mov_start', 'arrive_home', None, 100, 120, 'c11'),
]

def reward_func(assignments, decision_variables):
    val = 600
    for assignment in assignments:
        if assignment.var.name == 'movie':
            if assignment.val == 'good':
                val -= 0
            elif assignment.val == 'bad':
                val -= 495
        if assignment.var.name == 'restaurant':
            if assignment.val == 'chinese':
                val -= 0
            elif assignment.val == 'korean':
                val -= 50
    return val

reward_func = {
    'movie': {'good': 500, 'bad': 5},
    'restaurant': {'chinese': 50, 'korean': 0},
}

original_problem = BCDRSolver(reward_func)
original_problem.add_variable('restaurant', type='finite_domain', domain=['chinese', 'korean'], decision_variable=True)
original_problem.add_variable('movie', type='finite_domain', domain=['good', 'bad'], decision_variable=True)
for constraint in constraints:
    original_problem.add_temporal_constraint(constraint)

print("Running algorithm...")
solvable, reward, assignments, relaxations, conflicts = original_problem.run()

if solvable:
    print("Solution:")
    print("Reward:", reward)
    print("Assignments:", assignments)
    print("Relaxations:", relaxations)
else:
    print("Unfeasible due to conflicts:")
    for assignment, conflict in conflicts.items():
        print("")
        print(assignment)
        for conflict in conflict:
            print(conflict)

print("")

tc_no = 0
new_prob = copy.deepcopy(original_problem)
original_conflicts = conflicts
original_assignments = assignments
original_assignment_vars = set(assignment.var.name for assignment in original_assignments)
original_assignment_dict = {assignment.var.name : assignment.val for assignment in original_assignments}
original_relaxations = relaxations
while True:
    try:
        print("Suggest alternative:")
        selection = '0'
        while selection not in ('1', '2'):
            print("1) Temporal")
            print("2) Assignment")
            selection = input()
            print("")
        if selection == '1':
            start = input("Start event: ")
            end = input("End event: ")
            lb = float(input("Lower bound: "))
            ub = float(input("Upper bound: "))
            constraint = TPNConstraint(start, end, None, lb, ub, f'u{tc_no}')
            tc_no += 1
            new_prob.add_temporal_constraint(constraint)
        elif selection == '2':
            constraint = input("New assignment or constraint: ")
            new_prob.add_constraint(constraint)

        print("Running algorithm...")
        solvable, reward, assignments, relaxations, conflicts = new_prob.run()
        print("")
        if solvable:
            print("Solution:")
            print("Reward:", reward)
            print("Assignments:", assignments)
            print("Relaxations:", relaxations)
            print("")

            max_reward_diff = 0
            max_reward_diff_reason = None
            for assignment in assignments:
                if assignment.var.name in original_assignment_dict:
                    var_name = assignment.var.name
                    original_val = original_assignment_dict[var_name]
                    if var_name in reward_func:
                        reward_diff = reward_func[var_name][original_val] - reward_func[var_name][assignment.val]
                        print(f"{var_name:>15}: {original_val + ' --> ' + assignment.val:>15}{'Diff: ' + str(-reward_diff):>15}")
                        if reward_diff > max_reward_diff:
                            max_reward_diff = reward_diff
                            max_reward_diff_reason = f"changed assignment of {var_name} from {original_val} to {assignment.val}"

            if relaxations is not None:
                relaxation_diff = original_relaxations.objective_value - relaxations.objective_value
                if relaxation_diff > max_reward_diff:
                    max_reward_diff = relaxation_diff
                    max_reward_diff_reason = f"relaxation"

            print(f"With {constraint}, {max_reward_diff_reason} leads to loss of reward by {max_reward_diff}.")
        else:
            print("Unfeasible due to conflicts:")
            for assignment, conflict in conflicts.items():
                print(assignment)
                for conflict in conflict:
                    print(conflict)
                print("")

        resp = input("Reset to original problem? ")
        if resp.upper()[0] == 'Y':
            new_prob = copy.deepcopy(original_problem)

    except ValueError:
        print("Incorrect type")
    print("")
