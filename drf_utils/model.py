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
        self.epsilon = Real(f"epsilon")

        self.resources = [
            [Real(f"resource[t = {t}][j = {j}]") for j in range(self.NUM_RESOURCES)]
            for t in range(self.NUM_TIMESTEPS + 1)
        ]

        self.consumed = [
            [Real(f"consumed[t = {t}][j = {j}]") for j in range(self.NUM_RESOURCES)]
            for t in range(self.NUM_TIMESTEPS + 1)
        ]

        # User utilities -- Common among all users in progressive filling
        self.alphas = [Int(f"alpha[t = {t}]") for t in range(self.NUM_TIMESTEPS + 1)]

        self.org_demands = [
            [
                Real(f"demand_original[userId = {i}][resource = {j}]")
                for j in range(self.NUM_RESOURCES)
            ]
            for i in range(self.NUM_USERS)
        ]

        self.normalized_demands = [
            [
                Real(f"demand_scaled[userId = {i}][resource = {j}]")
                for j in range(self.NUM_RESOURCES)
            ]
            for i in range(self.NUM_USERS)
        ]

        self.dominant_shares_indices = [
            Int(f"s_{i}_indx") for i in range(self.NUM_USERS)
        ]
        self.unscaled_max_shared = [
            Real(f"s_{i}_unscaled") for i in range(self.NUM_USERS)
        ]
        self.dominant_shares = [Real("s_{i}") for i in range(self.NUM_USERS)]

        self.constraints.append(And(self.epsilon > 0.0, self.epsilon <= 1.0))
        self.process_given_demands(given_demands)
        self.resources_and_consumed_are_bdd()
        self.resources_and_consumed_are_monotonic()
        self.saturate_a_resource_at_end()
        self.alphas_are_positive_and_strictly_monotonic()
        self.demands_are_bdd()
        self.define_dominant_shares()
        self.define_normalized_demands()
        self.no_overallocation_constraints()

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

    def alphas_are_positive_and_strictly_monotonic(self):
        for t, alpha in enumerate(self.alphas):
            self.constraints.append((alpha == 0) if (t == 0) else (0 <= alpha))
        for t in range(self.NUM_TIMESTEPS):
            self.constraints.append(self.alphas[t] < self.alphas[t + 1])

    def demands_are_bdd(self):
        for i in range(len(self.org_demands)):
            for j in range(len(self.org_demands[i])):
                # no zero demand allowed
                self.constraints.append(
                    And(0.0 < self.org_demands[i][j], self.org_demands[i][j] <= 1.0)
                )
                self.constraints.append(
                    And(
                        0.0 < self.normalized_demands[i][j],
                        self.normalized_demands[i][j] <= self.epsilon,
                    )
                )

    def no_overallocation_constraints(self):
        for t in range(self.NUM_TIMESTEPS + 1):
            for j in range(self.NUM_RESOURCES):
                consumed_expr = sum(
                    self.alphas[t] * self.normalized_demands[i][j]
                    for i in range(self.NUM_USERS)
                )
                self.constraints.append(self.consumed[t][j] == consumed_expr)
                self.constraints.append(self.consumed[t][j] <= 1.0)
                self.constraints.append(self.resources[t][j] == 1 - consumed_expr)

    def define_dominant_shares(self):
        for i in range(self.NUM_USERS):
            self.constraints.append(
                And(
                    self.dominant_shares_indices[i] >= 0,
                    self.dominant_shares_indices[i] < self.NUM_RESOURCES,
                )
            )

            for j in range(self.NUM_RESOURCES):
                comparisons = [
                    self.org_demands[i][j] >= self.org_demands[i][j2]
                    for j2 in range(self.NUM_RESOURCES)
                ]

                self.constraints.append(
                    Implies(self.dominant_shares_indices[i] == j, And(*comparisons))
                )

                self.constraints.append(
                    Implies(
                        self.dominant_shares_indices[i] == j,
                        self.unscaled_max_shared[i] == self.org_demands[i][j],
                    )
                )

    def define_normalized_demands(self):
        for i in range(self.NUM_USERS):
            scale = self.epsilon / self.unscaled_max_shared[i]
            self.constraints.extend(
                [
                    self.normalized_demands[i][j] == scale * self.org_demands[i][j]
                    for j in range(self.NUM_RESOURCES)
                ]
            )
