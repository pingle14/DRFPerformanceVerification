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


# NOTE: We guarantee after T timesteps you reach a terminal state.
# This ensures the algorithm steps


def check_sat_helper(s: Solver, fn: str, T: int, U: int, R: int):
    res = s.check()
    if res == sat:
        m = s.model()
        l = sorted([f"{d} = {m[d]}" for d in m])
        with open(f"{fn}.txt", "w") as f:
            for e in l:
                print(e)
                f.write(str(e) + "\n")
        return False
    return True


def check_sat(s: Solver, fn: str, T: int, U: int, R: int, verbose=True):
    if verbose:
        print(f"Checking {fn} ... ", end="")
    result = check_sat_helper(s, fn, T, U, R)
    if verbose:
        print("PASS" if result else "FAIL")
    return result


# "For simplicity, assume all users use all resources"
def each_user_saturated_resource_DRF(T=5, U=2, R=2, verbose=True):
    s = Solver()
    state = State(T, U, R)
    s.add(state.constraints)
    # s.add(all_allocations(state, drf_algorithm_constraints))
    # s.add(state.terminal == True)

    # terminal --> forall i, exists j, sat(i, j)
    # Contradiction --> exists i, forall j, unsat(i, j)
    for i in range(state.NUM_USERS):
        # get dominant
        all_unsaturated = True
        for j in range(state.NUM_RESOURCES):
            # change user i to (alpha_i + 1). Keep other users the same.
            # Show how this overconsumes resources
            consumed_expr = sum(
                (state.alphas[state.NUM_TIMESTEPS] + If(i2 == i, 1, 0))
                * state.normalized_demands[i2][j]
                for i2 in range(state.NUM_USERS)
            )

            all_unsaturated = And(all_unsaturated, consumed_expr <= 1.0)
        s.add(all_unsaturated)  # Should yield unsat

    return check_sat(s, "lemma8", T, U, R, verbose)


def test_each_user_saturated_resource_DRF():
    print("Checking lemma 8 for all T, U, R (bdd) ... ", end="")
    for T in range(1, 5):
        for U in range(1, 2):
            for R in range(1, 2):
                assert each_user_saturated_resource_DRF(T, U, R, False)
    print("PASS")


# Utilitiy is alpha
def drf_pareto_efficient(T=2, U=2, R=2, verbose=True):
    s = Solver()
    state = State(T, U, R)
    s.add(state.constraints)
    # s.add(all_allocations(state, drf_algorithm_constraints))
    # s.add(state.terminal == True)

    new_alphas = [Int(f"alpha_new[t = {T}][i = {i}]") for i in range(state.NUM_USERS)]
    for i in range(state.NUM_USERS):
        # Add all new alloc constraints: chosen user improves. remainin users at least as good
        for i2 in range(state.NUM_USERS):
            constraint = (
                new_alphas[i] > state.alphas[T]
                if i == i2
                else new_alphas[i2] >= state.alphas[T]
            )
            s.add(constraint)

        all_unsaturated = True
        for j in range(state.NUM_RESOURCES):
            consumed_expr = sum(
                (new_alphas[i2]) * state.normalized_demands[i2][j]
                for i2 in range(state.NUM_USERS)
            )

            all_unsaturated = And(all_unsaturated, consumed_expr <= 1.0)
        s.add(all_unsaturated)  # Should yield unsat
    return check_sat(s, "pareto", T, U, R, verbose)


def test_drf_pareto_efficient():
    print("Checking pareto for all T, U, R (bdd) ... ", end="")
    for T in range(1, 5):
        for U in range(1, 2):
            for R in range(1, 2):
                assert drf_pareto_efficient(T, U, R, False)
    print("PASS")


def drf_envy_free(T=2, U=2, R=2, verbose=True):
    s = Solver()
    state = State(T, U, R)
    s.add(state.constraints)
    # s.add(all_allocations(state, drf_algorithm_constraints))
    # s.add(state.terminal == True)

    # User i envys user j
    def envy_condition(i, i2):
        conditions = []
        for j in range(state.NUM_RESOURCES):
            # If user i wants resource r, then user j must have strictly more of it than user i
            conditions.append(
                (state.alphas[state.NUM_TIMESTEPS] * state.normalized_demands[i2][j])
                > (state.alphas[state.NUM_TIMESTEPS] * state.normalized_demands[i][j])
            )
        return And(conditions)

    exists_envy = False
    for userI in range(state.NUM_USERS):
        for userJ in range(state.NUM_USERS):
            if userI != userJ:
                envy = envy_condition(userI, userJ)
                s.add(
                    Implies(
                        envy,
                        (state.alphas[state.NUM_TIMESTEPS][userJ])
                        == (state.alphas[state.NUM_TIMESTEPS][userI]),
                    )
                )
                exists_envy = Or(exists_envy, envy)

    s.add(exists_envy)
    return check_sat(s, "envy_free", T, U, R, verbose)


def test_drf_envy_free():
    print("Checking envy freedom for all T, U, R (bdd) ... ", end="")
    for T in range(1, 5):
        for U in range(1, 2):
            for R in range(1, 2):
                assert drf_envy_free(T, U, R, False)
    print("PASS")


# A user should not be able to allocate more
# tasks in a cluster partition consisting of 1/n of all resources
def drf_sharing_incentive(T=2, U=2, R=2, verbose=True):
    s = Solver()
    state = State(T, U, R)
    s.add(state.constraints)
    # s.add(all_allocations(state, drf_algorithm_constraints))
    # s.add(state.terminal == True)

    # show forall i. s_i >= 1/n
    """
    3/8, 3/8
    """
    exists_bad_sharing = False

    # all same dominant share --> should get 1/n resource
    common_share_indx = Int("common_share_indx")
    common_dominant_share = Real("common_dom_share")
    s.add(And(common_share_indx >= 0, common_share_indx < state.NUM_RESOURCES))
    s.add(common_dominant_share == 1 / state.NUM_USERS)
    all_equal = And(
        *[
            state.dominant_shares_indices[i] == common_share_indx
            for i in range(state.NUM_USERS)
        ]
    )
    s.add(common_dominant_share == (state.alphas[state.NUM_TIMESTEPS] * state.epsilon))

    for i in range(state.NUM_USERS):
        dominant_share = state.alphas[state.NUM_TIMESTEPS] * state.epsilon
        bad_alloc = dominant_share < (1 / state.NUM_USERS)
        exists_bad_sharing = Or(exists_bad_sharing, bad_alloc)
    s.add(exists_bad_sharing)
    return check_sat(s, "sharing_incentive", T, U, R, verbose)


def drf_strategy_proof(T, U, R):
    s = Solver()
    state = State(T, U, R)
    s.add(state.constraints)
    s.add(all_allocations(state, drf_algorithm_constraints))
    s.add(state.terminal == True)


def drf_paper_example():
    st = State(6, 2, 2, [["1/9", "4/18"], ["3/9", "1/18"]])
    s = Solver()
    print("Adding Constraints")
    s.add(st.constraints)
    s.add(all_allocations(st, drf_algorithm_constraints))
    "Add required state transitions"
    # s.add(st.epsilon == RealVal("2/7"))
    # s.add(st.alphas[0][0] == 0)
    # s.add(st.alphas[0][1] == 0)
    # s.add(st.alphas[1][0] == 0)
    # s.add(st.alphas[1][1] == 1)
    # s.add(st.alphas[2][0] == 1)
    # s.add(st.alphas[2][1] == 1)
    # s.add(st.alphas[3][0] == 1)
    # s.add(st.alphas[3][1] == 2)
    # s.add(st.alphas[4][0] == 2)
    # s.add(st.alphas[4][1] == 2)
    # s.add(st.alphas[5][0] == 3)
    # s.add(st.alphas[5][1] == 2)
    # s.add(st.alphas[6][0] == 3)
    # s.add(st.alphas[6][1] == 2)

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


# drf_paper_example()
test_each_user_saturated_resource_DRF()
test_drf_pareto_efficient()
test_drf_envy_free()
drf_sharing_incentive()
