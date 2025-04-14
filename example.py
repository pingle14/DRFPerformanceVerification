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


def drf_algorithm_constraints(T, s):
    return []


def all_allocations(s: Solver):
    constraints = []
    T = Timestep(0)
    while T.t < st.NUM_TIMESTEPS:
        constraints.extend(drf_algorithm_constraints(T, s))
        T = T.next()
    return constraints


st = State(5, 3, 1)
s = Solver()

print("Adding Constraints")
s.add(st.constraints)
s.add(all_allocations(s))

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
