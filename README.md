# Performance Verification of the Dominant Resource Fairness (DRF) Algorithm 

We formalize Dominant Resource Fairness (DRF) Algorithm in Rocq (a theorem prover language) and z3 (a SMT solver). 
* *Rocq Formalization*: We formalized DRF in Rocq using *Operational Small-Step Semantics*. We also proved Simulated Example from the paper works, DRF is deterministic, DRF cannot step after saturating resources. We explored DRF with varying demands and jobqueues and showed simulated example works
* *z3 Formalization*: Constructed z3 formalizaton of DRF. Proved Simulated Example works, DRF Allocation ensures each user has at least 1 saturated resource (Lemma in DRF paper), and DRF satisfies the *4 fairness properties* (Sharing Incentive, Strategy Proofness, Envy Freedom, Pareto Efficiency)