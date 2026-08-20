# AISO-01: optimize only inside the admissible set

The new control layer separates proposal quality from permission to act.

`D_t = {delta in A_t | Improve>0 and Risk<=rho and Validate and Permit and Safe and PreservesInv and RollbackWitness}`

`delta*_t = argmax_(delta in D_t) [alpha Improve - beta Risk - gamma Cost - lambda Entropy]`

An empty `D_t` produces `NO_OP`. A selected action still cannot teach the model until CSS applies it, post-verification succeeds, protected invariants remain true, and a receipt is issued. A failed postcheck activates the supplied rollback witness and blocks learning.

This is a formal selection contract, not a claim that the risk model or quality function is physically complete.

Code: [Lean core](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/AISOControlLoop.lean) · [reference selector](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/aiso-control-loop.mjs) · [blind corpus](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/tests/aiso-control-loop.test.mjs)

Shoulders: [Constrained Policy Optimization](https://arxiv.org/abs/1705.10528) · [Shielding](https://arxiv.org/abs/1708.08611) · [Simplex](https://www.sei.cmu.edu/library/an-architectural-description-of-the-simplex-architecture/) · [NIST AI RMF](https://doi.org/10.6028/NIST.AI.100-1)

