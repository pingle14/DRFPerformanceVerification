from z3 import *


class Config:
    NUM_RESOURCES = 2
    NUM_USERS = 2
    NUM_TIMESTEPS = 2


class Timestep:
    def __init__(self, t):
        self.t = t

    def next(self):
        return Timestep(self.t + 1)


class State:
    def __init__(self, num_timesteps, num_users, num_resources):
        self.NUM_TIMESTEPS = num_timesteps
        self.NUM_USERS = num_users
        self.NUM_RESOURCES = num_resources
        self.epsilon = Real(f"epsilon")
        self.epsilon_constraints = [And(self.epsilon > 0.0, self.epsilon <= 1.0)]
        self.resource_constraints = []
        self.user_constraints = []
        self.demand_constraints = []

        self.init_resource_constraints()
        self.init_user_alloc_constraints()
        self.init_user_demand_constraints()

        # TODO: fill in state transition constraints

        # TODO: maybe not required: Add constraint that sum_{i in [n]} (alpha_i * D_i) <= R

        self.constraints = []
        self.constraints.extend(self.demand_constraints)
        self.constraints.extend(self.resource_constraints)
        self.constraints.extend(self.epsilon_constraints)
        self.constraints.extend(self.user_constraints)

    def init_resource_constraints(self):
        self.resources = [
            [Real(f"resource[t = {t}][j = {j}]") for j in range(self.NUM_RESOURCES)]
            for t in range(self.NUM_TIMESTEPS)
        ]
        for t, resources_at_t in enumerate(self.resources):
            for resource in resources_at_t:
                resource_lim = (
                    resource == 1.0
                    if (t == 0)
                    else And(0.0 <= resource, resource <= 1.0)
                )
                self.resource_constraints.append(resource_lim)

    def init_user_alloc_constraints(self):
        self.user_alphas = [
            [Int(f"alpha[t = {t}][i = {i}]") for i in range(self.NUM_USERS)]
            for t in range(self.NUM_TIMESTEPS)
        ]
        for t, user_alphas_at_t in enumerate(self.user_alphas):
            for alpha_i in user_alphas_at_t:
                self.user_constraints.append(
                    (alpha_i == 0) if (t == 0) else (0 <= alpha_i)
                )

    def init_user_demand_constraints(self):
        self.user_demands = [
            [
                Real(f"orgDemand[userId = {i}][resource = {j}]")
                for j in range(self.NUM_RESOURCES)
            ]
            for i in range(self.NUM_USERS)
        ]
        for user_id, demand_vector in enumerate(self.user_demands):
            for demand in demand_vector:
                # no zero demand allowed
                self.user_constraints.append(And(0.0 < demand, demand <= 1.0))
        self.dominant_shares = [
            Real(f"dominant_share[userId = {i}]") for i in range(self.NUM_USERS)
        ]

        self.demand_constraints = []
        for i in range(self.NUM_USERS):
            for j in range(self.NUM_RESOURCES):
                self.demand_constraints.append(
                    self.dominant_shares[i] >= self.user_demands[i][j]
                )

        # (eps / s_i) * demand
        self.normalized_demands = [
            [
                Real(f"scaledDemand[userId = {i}][resource = {j}]")
                for j in range(self.NUM_RESOURCES)
            ]
            for i in range(self.NUM_USERS)
        ]

        for i in range(self.NUM_USERS):
            scale = self.epsilon / self.dominant_shares[i]
            self.demand_constraints.extend(
                [
                    self.normalized_demands[i][j] == scale * self.user_demands[i][j]
                    for j in range(self.NUM_RESOURCES)
                ]
            )


"""
state:
Time-invariant: 
    * User.demands: (n x m) ... d_i in [0,1] and dominant share
Change with time:
    * resource[t]: 1 --> 0 ... should be mono decreasing
    * User.Allocations[t][userId]
    * min dominant share = min(alpha_i * D_i)

"""
