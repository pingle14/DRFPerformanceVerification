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

        self.resource_constraints = []
        self.resources = [
            [Real(f"resource[t = {t}][j = {j}]") for j in range(num_resources)]
            for t in range(num_timesteps)
        ]
        for t, resources_at_t in enumerate(self.resources):
            for resource in resources_at_t:
                resource_lim = (
                    resource == 1.0
                    if (t == 0)
                    else And(0.0 <= resource, resource <= 1.0)
                )
                self.resource_constraints.append(resource_lim)

        self.user_constraints = []

        "alpha_i = number of times apply user_i demand vector"
        self.user_alphas = [
            [Int(f"alpha[t = {t}][i = {i}]") for i in range(num_users)]
            for t in range(num_timesteps)
        ]
        for t, user_alphas_at_t in enumerate(self.user_alphas):
            for alpha_i in user_alphas_at_t:
                self.user_constraints.append(
                    (alpha_i == 0) if (t == 0) else (0 <= alpha_i)
                )


"""
state:
Time-invariant: 
    * User.demands: (n x m) ... d_i in [0,1]
Change with time:
    * resource[t]: 1 --> 0 ... should be mono decreasing
    * User.Allocations[t][userId]

"""
