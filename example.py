from z3 import *
from drf_utils.model import *

"""
Bounded Model Checking:
- Express invariants in temporal logic

Params: m resources, n users
R = [1.....1] --> s_i = max(d_ik) over k in [m]
alpha = [1 2 3 ..] = num times allocated
D = [[1/9, 4/18]; [3/9, 1/18]]
  = [[d_11, d_12]; [d_21, d_22]]


Constraints on input (demand vectors): 0 < D < 1

R[t] = R[t - 1]
D_i = (eps / max(d_ik)) [d_i1, .. d_im]

Noramlized Demand Vectors:
    D = [[1/9, 4/18]; [3/9, 1/18]]
    * D_A = (18 eps / 4)[1/9, 4/18] = [eps/2, eps]
    * D_B = (9 eps / 3)[3/9, 1/18] = [eps, eps/6]


A_i[t] = alpha_i[t] * D_i
forall k in [m]. R_m[t] >= sum_{i in [n]} A_i[t] ... stop when violated


Actually, each new state should decrease resources. Terminate when there is a 0 resource


def continue_allocating(s : Solver):
    constraints = []
    T = Timestep(0, 0)
    while(T.t < cfg.NUM_TIMESTEPS):
        constraints.extend(drf_algorithm(T,  s))
        T = T.next()
    return constraints

    
def DRF_Algorithm(state):
    dominant_shares = get_user_domenant_shares(state)
    user_indx = argmin(dominant_shares)
    user_demands = state.demand[user_indx]

    # update state
    if state.consumed + user_demands <= state.resources:
        state.consumed += user_demands
        state.user_alloc[user_indx] += 1

    return state

"""


def drf_algorithm_constraints(T, state: State):
    state_transition_constraints = []
    t = T.t
    # TODO: Check if correct: Pick the min dom share user: user with min alpha_i[t]
    chosen_user = Int(f"chosen_user[t = {t}]")
    state_transition_constraints.append(
        And(chosen_user >= 0, chosen_user < state.NUM_USERS)
    )

    # Add the constraints for all users (compared to min_share)
    for i in range(state.NUM_USERS):
        current_share = state.alphas[t - 1][i]
        comparisons = [
            current_share <= state.alphas[t - 1][i2] for i2 in range(state.NUM_USERS)
        ]

        state_transition_constraints.append(
            Implies(chosen_user == i, And(*comparisons))
        )

    # TODO: alpha_i[t+1] =  (alpha_i[t] + 1) d_i <= 1 ? (alpha_i[t] + 1) : alpha_i[t]
    condition = True
    for j in range(state.NUM_RESOURCES):
        consumed_expr = sum(
            If(
                chosen_user == i,  # If user i is the chosen user
                state.alphas[t - 1][i] + 1,  # allocat this user
                state.alphas[t - 1][i],  # Otherwise, stay same
            )
            * state.normalized_demands[i][j]
            for i in range(state.NUM_USERS)
        )

        # Combine the constraints w And
        condition = And(condition, consumed_expr <= 1.0)

    for i in range(state.NUM_USERS):
        state_transition_constraints.append(
            Implies(
                chosen_user == i,  # Apply only when chosen_user == i
                state.alphas[t][i]
                == If(
                    condition,
                    state.alphas[t - 1][i] + 1,
                    state.alphas[t - 1][i],
                ),
            )
        )
    state_transition_constraints.extend(
        [
            Implies(Not(condition), state.resources[t][j] == state.resources[t - 1][j])
            for j in range(state.NUM_RESOURCES)
        ]
    )
    return state_transition_constraints


def all_allocations(state: State, state_transition_fn):
    constraints = []
    T = Timestep(1)
    while T.t <= state.NUM_TIMESTEPS:
        constraints.extend(state_transition_fn(T, state))
        T = T.next()
    return constraints


"For simplicity, assume all users use all resources"


def each_user_saturated_resource_DRF():
    s = Solver()
    # T = Int("*TIMESTEPS")
    # U = Int("*NUM_USERS")
    # R = Int("*NUM_RESOURCES")
    # s.add(And(0 < T, T <= 2, 0 < U, U <= 2, 0 < R, R <= 2))
    state = State(2, 2, 2)
    s.add(state.constraints)
    s.add(all_allocations(state, drf_algorithm_constraints))
    s.add(state.terminal == True)

    # terminal --> forall i, forall j, sat(i, j)
    # Contradiction --> exists i, exists j, unsat(i, j)
    for i in range(state.NUM_USERS):
        # get dominant
        all_unsaturated = False
        for j in range(state.NUM_RESOURCES):
            consumed_expr = sum(
                (state.alphas[state.NUM_TIMESTEPS][i] + 1)
                * state.normalized_demands[i][j]
                for i in range(state.NUM_USERS)
            )

            all_unsaturated = And(all_unsaturated, consumed_expr <= 1.0)
        s.add(Implies(state.terminal, all_unsaturated))  # Should yield unsat

    res = s.check()
    if res == sat:
        m = s.model()
        l = sorted([f"{d} = {m[d]}" for d in m])
        with open("lemma8.txt", "w") as f:
            for e in l:
                print(e)
                f.write(str(e) + "\n")
    else:
        print("Lemma 8 QED")


each_user_saturated_resource_DRF()


def drf_paper_example():
    st = State(6, 2, 2, [["1/9", "4/18"], ["3/9", "1/18"]])
    s = Solver()
    print("Adding Constraints")
    s.add(st.constraints)
    s.add(all_allocations(st, drf_algorithm_constraints))
    "Add required state transitions"
    s.add(st.epsilon == RealVal("2/7"))
    s.add(st.alphas[0][0] == 0)
    s.add(st.alphas[0][1] == 0)
    s.add(st.alphas[1][0] == 0)
    s.add(st.alphas[1][1] == 1)
    s.add(st.alphas[2][0] == 1)
    s.add(st.alphas[2][1] == 1)
    s.add(st.alphas[3][0] == 1)
    s.add(st.alphas[3][1] == 2)
    s.add(st.alphas[4][0] == 2)
    s.add(st.alphas[4][1] == 2)
    s.add(st.alphas[5][0] == 3)
    s.add(st.alphas[5][1] == 2)
    s.add(st.alphas[6][0] == 3)
    s.add(st.alphas[6][1] == 2)

    print("Checking")
    res = s.check()
    print(f"example 1 {res}")

    if res == sat:
        m = s.model()
        l = sorted([f"{d} = {m[d]}" for d in m])
        with open("example1.txt", "w") as f:
            for e in l:
                print(e)
                f.write(str(e) + "\n")
