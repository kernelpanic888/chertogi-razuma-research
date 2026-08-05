# AZ-00: Agent Zero execution gate

`V_0, V_ext, Safe : X -> {0,1}`

`Exec_0(X)=some(X) iff V_0(X)=1 and V_ext(X)=1 and Safe(X)=1`; otherwise `none`.

Agent Zero acts only when self-validation, external validation, and the safety contour accept the same action. Full agreement returns that unchanged action. One zero means no action. Lean proves the conjunction semantics, and the executable test covers all eight binary combinations.

[Lean core](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/AgentZeroValidationKernel.lean) · [truth table](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/tests/agent-zero-validation-kernel.test.mjs)
