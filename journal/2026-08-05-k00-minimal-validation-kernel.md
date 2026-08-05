# K-00: interface closure

`Act_I(a,b)=V_A(a) and V_B(b) and C_I(a,b)`

`Exec_I(a,b)=some(a,b)` when the triple agrees; otherwise `none`.

Two validated states do not yet produce an act. The interface compatibility predicate closes the triple. Agreement yields the unchanged candidate act; one mismatch yields silence. Lean proves this conjunction semantics, and the executable test covers all eight binary combinations.

[Lean core](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/AISOValidationKernel.lean) · [truth table](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/tests/aiso-validation-kernel.test.mjs)
