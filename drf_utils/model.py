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
    def __init__(self, num_timesteps, num_users, num_resources, given_demands=None):
        self.NUM_TIMESTEPS = num_timesteps
        self.NUM_USERS = num_users
        self.NUM_RESOURCES = num_resources
        self.constraints = []
        self.epsilon = Real(f"epsilon")
        self.terminal = Bool("terminal")

        self.resources = [
            [Real(f"resource[t = {t}][j = {j}]") for j in range(self.NUM_RESOURCES)]
            for t in range(self.NUM_TIMESTEPS + 1)
        ]

        self.consumed = [
            [Real(f"consumed[t = {t}][j = {j}]") for j in range(self.NUM_RESOURCES)]
            for t in range(self.NUM_TIMESTEPS + 1)
        ]

        self.alphas = [
            [Int(f"alpha[t = {t}][i = {i}]") for i in range(self.NUM_USERS)]
            for t in range(self.NUM_TIMESTEPS + 1)
        ]

        self.total_alphas = [
            Int(f"alpha_sum[t = {t}]") for t in range(self.NUM_TIMESTEPS + 1)
        ]

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

        self.process_given_demands(given_demands)
        self.define_terminal_constraints()
        self.constraints.append(And(self.epsilon > 0.0, self.epsilon <= 1.0))
        self.resources_are_bdd()
        self.resources_are_mono_dec()
        self.consumed_are_mono_inc()
        self.no_overallocation_constraints()
        self.alphas_are_positive()
        self.alphas_are_monotonic_inc()
        self.define_total_alphas()  # Cant alloc multiple alphas at one. Can only choose 1 user
        self.demands_are_bdd()
        self.define_dominant_shares()
        self.define_normalized_demands()

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

    def define_terminal_constraints(self):
        terminal_condition = False
        for j, resource in enumerate(self.resources[self.NUM_TIMESTEPS]):
            terminal_condition = Or(
                terminal_condition,
                resource == self.resources[self.NUM_TIMESTEPS - 1][j],
            )
        self.constraints.append(Implies(terminal_condition, self.terminal))
        self.constraints.append(Implies(Not(terminal_condition), Not(self.terminal)))

    def resources_are_bdd(self):
        for t, resources_at_t in enumerate(self.resources):
            for resource in resources_at_t:
                self.constraints.append(And(0.0 <= resource, resource <= 1.0))
                if t == 0:
                    self.constraints.append(1.0 == resource)

    def resources_are_mono_dec(self):
        for j in range(self.NUM_RESOURCES):
            for t in range(self.NUM_TIMESTEPS):
                self.constraints.append(
                    self.resources[t][j] >= self.resources[t + 1][j]
                )

    def alphas_are_positive(self):  # can never have a negative alloc count
        for t, alphas_at_t in enumerate(self.alphas):
            for alpha_i in alphas_at_t:
                self.constraints.append((alpha_i == 0) if (t == 0) else (0 <= alpha_i))

    def alphas_are_monotonic_inc(self):
        for i in range(self.NUM_USERS):
            for t in range(self.NUM_TIMESTEPS):
                self.constraints.append(self.alphas[t][i] <= self.alphas[t + 1][i])

    def define_total_alphas(self):
        self.constraints.append(self.total_alphas[0] == 0)
        for t in range(self.NUM_TIMESTEPS + 1):
            self.constraints.append(
                self.total_alphas[t]
                == sum([self.alphas[t][i] for i in range(self.NUM_USERS)])
            )

        for t in range(self.NUM_TIMESTEPS):
            # Sum all alphas ... should be <= 1 greater than one before
            difference = self.total_alphas[t + 1] - self.total_alphas[t]
            self.constraints.append(Or(difference == 0, difference == self.NUM_USERS))

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

    def consumed_are_mono_inc(self):
        for j in range(self.NUM_RESOURCES):
            for t in range(self.NUM_TIMESTEPS):
                self.constraints.append(self.consumed[t][j] <= self.consumed[t + 1][j])

    def no_overallocation_constraints(self):
        for t in range(self.NUM_TIMESTEPS + 1):
            for j in range(self.NUM_RESOURCES):
                consumed_expr = sum(
                    self.alphas[t][i] * self.normalized_demands[i][j]
                    for i in range(self.NUM_USERS)
                )
                self.constraints.append(self.consumed[t][j] == consumed_expr)
                self.constraints.append(self.consumed[t][j] <= 1.0)
                if t > 0:
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


"""
state:
Time-invariant: 
    * DONE: User.demands: (n x m) ... d_i in [0,1] and dominant share
Change with time:
    * DONE: resource[t]: 1 --> 0 ... should be mono decreasing
    * DONE: User.Allocations[t][userId]
    * min dominant share = min(alpha_i * D_i)

"""
