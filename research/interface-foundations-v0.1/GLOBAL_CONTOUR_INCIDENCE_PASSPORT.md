# Passport: IF-BS-12

## Name

Interior two-sided contour incidence.

## Question

Can a local contour terminate at the finite frame, and does every exact crossing vertex have continuations from both sides?

## Formal claims

- The radial threshold is strictly below the squared offset of the outer frame for every `m>0`.
- Every outer-frame node is outside.
- No horizontal or vertical outer-frame edge crosses the threshold.
- Every crossing edge is strictly interior in its transverse coordinate.
- Every horizontal crossing belongs to active cells below and above.
- Every vertical crossing belongs to active cells left and right.

## Verification rule

The main Lean module and separate import audit must compile. The audit reconstructs the strict boundary estimate, both interiority theorems, and both two-sided segment constructions. No `axiom`, `sorry`, or `admit` declaration is allowed.

## Verification result

- Lean 4.32.1 accepts the main module and the separate import audit.
- The source gap scan is clean.
- The strict outer-frame estimate reports only `propext` and `Quot.sound`.
- Interiority and the two segment constructions additionally report `Classical.choice`, inherited from the finite filtered side representation.

## Honest boundary

Proved: no frame termination and existence of two canonical incident local segments at every crossing edge.

Not proved: uniqueness of those incidences among all cell-side representations, exact global degree two, mod-two boundary cancellation, cycle decomposition, or uniqueness of the radial cycle.

## Next step

IF-BS-13: classify all cell incidences of each canonical edge and prove that the global polygonal chain has zero boundary.
