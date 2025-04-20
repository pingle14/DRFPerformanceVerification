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


def alphas_nonneg_and_strictly_monotonic(alphas, state: State):
    constraints = []
    for t, alpha in enumerate(alphas):
        constraints.append((alpha == 0) if (t == 0) else (0 <= alpha))
        # constraints.append(alpha == t)  # For paper example to get epsilon = 1/9
    for t in range(len(alphas) - 1):
        constraints.append(alphas[t] < alphas[t + 1])
    return constraints


def define_dominant_shares(dominant_shares_indices, unscaled_max_shared, state: State):
    constraints = []
    for i in range(state.NUM_USERS):
        constraints.append(
            And(
                dominant_shares_indices[i] >= 0,
                dominant_shares_indices[i] < state.NUM_RESOURCES,
            )
        )

        for j in range(state.NUM_RESOURCES):
            comparisons = [
                state.org_demands[i][j] >= state.org_demands[i][j2]
                for j2 in range(state.NUM_RESOURCES)
            ]

            constraints.append(
                Implies(
                    dominant_shares_indices[i] == j,
                    And(
                        unscaled_max_shared[i] == state.org_demands[i][j],
                        *comparisons,
                    ),
                )
            )
    return constraints


def define_scaled_demands(epsilon, unscaled_max_shared, scaled_demands, state):
    constraints = []
    for i in range(state.NUM_USERS):
        scale = epsilon / unscaled_max_shared[i]
        constraints.extend(
            [
                And(
                    scaled_demands[i][j] == scale * state.org_demands[i][j],
                    scaled_demands[i][j] > 0,
                    scaled_demands[i][j] <= epsilon,
                )
                for j in range(state.NUM_RESOURCES)
            ]
        )
    return constraints


def no_overallocation_constraints(alphas, scaled_demands, state):
    constraints = []
    for t in range(state.NUM_TIMESTEPS + 1):
        for j in range(state.NUM_RESOURCES):
            consumed_expr = sum(
                alphas[t] * scaled_demands[i][j] for i in range(state.NUM_USERS)
            )
            constraints.append(state.consumed[t][j] == consumed_expr)
    return constraints


def drf_progressive_filling(state):
    # User utilities -- Common among all users in progressive filling
    constraints = []
    epsilon = Real(f"epsilon")
    alphas = [Int(f"alpha[t = {t}]") for t in range(state.NUM_TIMESTEPS + 1)]

    scaled_demands = [
        [
            Real(f"demand_scaled[userId = {i}][resource = {j}]")
            for j in range(state.NUM_RESOURCES)
        ]
        for i in range(state.NUM_USERS)
    ]

    dominant_shares_indices = [Int(f"s_{i}_indx") for i in range(state.NUM_USERS)]
    unscaled_max_shared = [Real(f"s_{i}_unscaled") for i in range(state.NUM_USERS)]

    constraints.append(And(epsilon > 0.0, epsilon <= 1.0))
    constraints.extend(alphas_nonneg_and_strictly_monotonic(alphas, state))
    constraints.extend(
        define_dominant_shares(dominant_shares_indices, unscaled_max_shared, state)
    )
    constraints.extend(
        define_scaled_demands(epsilon, unscaled_max_shared, scaled_demands, state)
    )
    constraints.extend(no_overallocation_constraints(alphas, scaled_demands, state))

    return constraints, {
        "alphas": alphas,
        "scaled_demands": scaled_demands,
        "epsilon": epsilon,
    }


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
    drf_constraints, vars = drf_progressive_filling(state)
    s.add(state.constraints)
    s.add(drf_constraints)

    # terminal --> forall i, exists j, sat(i, j)
    # Contradiction --> exists i, forall j, unsat(i, j)
    exists_unsat_user = False
    for i in range(state.NUM_USERS):
        # get dominant
        all_unsaturated = True
        for j in range(state.NUM_RESOURCES):
            # change user i to (alpha_i + 1). Keep other users the same.
            # Show how this overconsumes resources
            consumed_expr = sum(
                (vars["alphas"][state.NUM_TIMESTEPS] + If(i2 == i, 1, 0))
                * vars["scaled_demands"][i2][j]
                for i2 in range(state.NUM_USERS)
            )

            all_unsaturated = And(all_unsaturated, consumed_expr <= 1.0)
        exists_unsat_user = Or(exists_unsat_user, all_unsaturated)
    s.add(exists_unsat_user)  # Should yield unsat

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
    drf_constraints, vars = drf_progressive_filling(state)
    s.add(state.constraints)
    s.add(drf_constraints)

    pareto_inefficient = False
    for i in range(state.NUM_USERS):
        # Add all new alloc constraints: chosen user improves. remainin users at least as good
        new_alpha = Int(f"alpha_new[t = {T}][i = {i}]")
        new_alpha_better = new_alpha > vars["alphas"][T]

        all_unsaturated = True
        for j in range(state.NUM_RESOURCES):
            consumed_expr = sum(
                (new_alpha if i == i2 else vars["alphas"][T])
                * vars["scaled_demands"][i2][j]
                for i2 in range(state.NUM_USERS)
            )

            all_unsaturated = And(all_unsaturated, consumed_expr <= 1.0)

        user_i_pareto_inefficient = And(new_alpha_better, all_unsaturated)
        pareto_inefficient = Or(pareto_inefficient, user_i_pareto_inefficient)
    s.add(pareto_inefficient)
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
    drf_constraints, vars = drf_progressive_filling(state)
    s.add(state.constraints)
    s.add(drf_constraints)

    # User i envys user j
    def envy_condition(i, i2):
        conditions = []
        for j in range(state.NUM_RESOURCES):
            # If user i wants resource r, then user j must have strictly more of it than user i
            conditions.append(
                (vars["alphas"][state.NUM_TIMESTEPS] * vars["scaled_demands"][i2][j])
                > (vars["alphas"][state.NUM_TIMESTEPS] * vars["scaled_demands"][i][j])
            )
        return And(conditions)

    exists_envy = False
    for userI in range(state.NUM_USERS):
        for userJ in range(state.NUM_USERS):
            if userI != userJ:
                envy = envy_condition(userI, userJ)
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
    drf_constraints, vars = drf_progressive_filling(state)
    s.add(state.constraints)
    s.add(drf_constraints)

    # show forall i. s_i >= 1/n
    dominant_share = vars["alphas"][state.NUM_TIMESTEPS] * vars["epsilon"]
    exists_bad_sharing = dominant_share < (1 / state.NUM_USERS)
    s.add(exists_bad_sharing)
    return check_sat(s, "sharing_incentive", T, U, R, verbose)


def test_drf_sharing_incentive():
    print("Checking sharing incentive for all T, U, R (bdd) ... ", end="")
    for T in range(1, 5):
        for U in range(1, 2):
            for R in range(1, 2):
                assert drf_sharing_incentive(T, U, R, False)
    print("PASS")


def drf_strategy_proof(T=2, U=2, R=2, verbose=True):
    s = Solver()
    state = State(T, U, R)
    drf_constraints, vars = drf_progressive_filling(state)
    s.add(state.constraints)
    s.add(drf_constraints)

    # TODO: determine property given a user. show it doesnt work for any user
    lying_wins = False
    for i in range(state.NUM_USERS):
        unscaled_new_demand = [
            Real(f"lie_D{i}{j}_unscaled") for j in range(state.NUM_RESOURCES)
        ]
        normalized_new_demand = [
            Real(f"lie_D{i}{j}_scaled") for j in range(state.NUM_RESOURCES)
        ]
        new_dom_share_indx = Int(f"lie_s_{i}_indx")
        new_dom_share = Int(f"lie_s_{i}")
        unscaled_new_is_different = [
            And(
                unscaled_new_demand[j] != state.org_demands[i][j],
                unscaled_new_demand[j] > 0.0,
                unscaled_new_demand[j] <= 1.0,
            )
            for j in range(state.NUM_RESOURCES)
        ]
        unscaled_new_is_different = And(*unscaled_new_is_different)
        new_dom_share_indx_is_bdd = And(
            new_dom_share_indx >= 0,
            new_dom_share_indx < state.NUM_RESOURCES,
        )

        # Get max dom share index
        index_is_max = []
        for j in range(state.NUM_RESOURCES):
            comparisons = [
                unscaled_new_demand[j] >= unscaled_new_demand[j2]
                for j2 in range(state.NUM_RESOURCES)
            ]

            index_is_max.append(Implies(new_dom_share_indx == j, And(*comparisons)))
            index_is_max.append(
                Implies(
                    new_dom_share_indx == j,
                    new_dom_share == unscaled_new_demand[j],
                )
            )
        index_is_max = And(*index_is_max)

        # Get scaled demand vector
        scale = vars["epsilon"] / new_dom_share
        normalized_is_normalized = And(
            *[
                normalized_new_demand[j] == scale * unscaled_new_demand[j]
                for j in range(state.NUM_RESOURCES)
            ]
        )

        # New normalized is better
        lying_is_better = And(
            *[
                normalized_new_demand[j] > vars["scaled_demands"][i][j]
                for j in range(state.NUM_RESOURCES)
            ]
        )

        lying_wins = Or(
            lying_wins,
            And(
                unscaled_new_is_different,
                new_dom_share_indx_is_bdd,
                index_is_max,
                normalized_is_normalized,
                lying_is_better,
            ),
        )

    s.add(lying_wins)
    return check_sat(s, "strategy_proof", T, U, R, verbose)


def test_drf_strategy_proof():
    print("Checking strategy proofness for all T, U, R (bdd) ... ", end="")
    for T in range(1, 5):
        for U in range(1, 2):
            for R in range(1, 2):
                assert drf_strategy_proof(T, U, R, False)
    print("PASS")


def drf_paper_example():
    state = State(6, 2, 2, [["1/9", "4/18"], ["3/9", "1/18"]])
    s = Solver()
    print("Adding Constraints")
    drf_constraints, vars = drf_progressive_filling(state)
    s.add(state.constraints)
    s.add(drf_constraints)
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


drf_paper_example()
test_each_user_saturated_resource_DRF()
test_drf_pareto_efficient()
test_drf_envy_free()
test_drf_sharing_incentive()
test_drf_strategy_proof()
# drf_paper_example()
