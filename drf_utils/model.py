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


class Resource:
    """
    Per resource variables and constraints
    """

    def __init__(self, id: int, num_timesteps: int):
        self.constraints = []
        self.resourceId = id

        self.allocations = [
            Real(f"resource[{self.resourceId}].alloc[{i}]")
            for i in range(num_timesteps + 1)
        ]

        for i, stage_alloc in enumerate(self.allocations):
            self.constraints.append(And(0.0 <= stage_alloc, stage_alloc <= 1.0))
            if i == 0:
                self.constraints.append(stage_alloc == 1.0)


class User:

    def __init__(self, id, num_timesteps, demand_vector):
        self.userId = id

    def __repr__(self):
        return str(self.userId)

    # return constaints on user at timestep i
    def update_state(self, T): ...
