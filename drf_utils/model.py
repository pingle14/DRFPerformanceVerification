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


# NOTE: We guarantee after T timesteps you reach a terminal state.
# This ensures the algorithm steps
class State:
    def __init__(self, num_timesteps, num_users, num_resources, given_demands=None):
        self.NUM_TIMESTEPS = num_timesteps
        self.NUM_USERS = num_users
        self.NUM_RESOURCES = num_resources
        self.constraints = []

        self.resources = [
            [Real(f"resource[t = {t}][j = {j}]") for j in range(self.NUM_RESOURCES)]
            for t in range(self.NUM_TIMESTEPS + 1)
        ]

        self.consumed = [
            [Real(f"consumed[t = {t}][j = {j}]") for j in range(self.NUM_RESOURCES)]
            for t in range(self.NUM_TIMESTEPS + 1)
        ]

        self.org_demands = [
            [
                Real(f"demand_original[userId = {i}][resource = {j}]")
                for j in range(self.NUM_RESOURCES)
            ]
            for i in range(self.NUM_USERS)
        ]

        self.process_given_demands(given_demands)
        self.resources_and_consumed_are_bdd()
        self.resources_and_consumed_are_monotonic()
        self.saturate_a_resource_at_end()
        self.demands_are_bdd()

    def process_given_demands(self, given_demands):
        if given_demands is not None:
            assert (
                len(given_demands) == self.NUM_USERS
                and len(given_demands[0]) == self.NUM_RESOURCES
            ), f"Demands dont match given dimensions"

            for i in range(self.NUM_USERS):
                for j in range(self.NUM_RESOURCES):
                    demand_val = RealVal(given_demands[i][j])  # Force to be real
                    self.constraints.append(self.org_demands[i][j] == demand_val)

    def resources_and_consumed_are_bdd(self):
        self.constraints.append(
            And(*[1.0 == self.resources[0][j] for j in range(self.NUM_RESOURCES)])
        )
        self.constraints.append(
            And(*[0.0 == self.consumed[0][j] for j in range(self.NUM_RESOURCES)])
        )
        for t in range(len(self.resources)):
            for j in range(len(self.resources[t])):
                self.constraints.append(
                    And(
                        0.0 <= self.resources[t][j],
                        self.resources[t][j] <= 1.0,
                        0.0 <= self.consumed[t][j],
                        self.consumed[t][j] <= 1.0,
                    )
                )
                self.constraints.append(self.resources[t][j] == 1 - self.consumed[t][j])

    def resources_and_consumed_are_monotonic(self):
        for j in range(self.NUM_RESOURCES):
            for t in range(self.NUM_TIMESTEPS):
                self.constraints.append(
                    And(
                        self.resources[t][j] >= self.resources[t + 1][j],  # mono dec
                        self.consumed[t][j] <= self.consumed[t + 1][j],  # mono inc
                    )
                )

    def saturate_a_resource_at_end(self):
        exists_zero_resource = False
        for j in range(self.NUM_RESOURCES):
            exists_zero_resource = Or(
                exists_zero_resource, self.resources[self.NUM_TIMESTEPS][j] == 0.0
            )
        self.constraints.append(exists_zero_resource)

    def demands_are_bdd(self):
        for i in range(len(self.org_demands)):
            for j in range(len(self.org_demands[i])):
                # no zero demand allowed
                self.constraints.append(
                    And(0.0 < self.org_demands[i][j], self.org_demands[i][j] <= 1.0)
                )
