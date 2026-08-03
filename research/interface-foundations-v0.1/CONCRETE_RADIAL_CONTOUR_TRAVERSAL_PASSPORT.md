# Passport: IF-BS-15

## Name

Concrete radial contour incidence traversal.

## Question

Does the actual finite radial marching-squares contour satisfy the abstract closed-cycle kernel?

## Objects

- A proof-carrying cell-side crossing state.
- The unique local partner in the same active cell.
- The unique shared partner across the same global crossing edge.
- Explicit enumeration of all bounded grid cells and sides.
- The IF-BS-14 alternating successor.

## Formal claims

- Every concrete state has exactly one distinct local partner.
- Every concrete state has exactly one distinct shared partner.
- Both partner maps are fixed-point-free involutions.
- The finite state list covers every concrete contour incidence.
- Every concrete state returns to itself after a strictly positive number of alternating steps.

## Verification rule

The main Lean module and an independent import audit must compile. The audit reconstructs both uniqueness claims and the final positive-period theorem. No `axiom`, `sorry`, or `admit` declaration is allowed.

## Verification result

Passed with Lean 4.32.1. The main module and independent audit compile, and the source-gap scan is empty. The final theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Honest boundary

Proved here: every concrete state lies on a finite closed cycle.

Not proved here: existence of only one cycle, identification of the intended radial component, geometric simplicity of its polygon, Hausdorff convergence to the continuum boundary, or any physical interpretation.

## Next step

IF-BS-16: prove connectedness or uniqueness of the concrete radial contour cycle.
