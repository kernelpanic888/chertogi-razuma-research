# Passport: IF-BS-11

## Name

Unambiguous local polygonal contour.

## Question

Do the exact edge crossings from IF-BS-10 assemble into one determinate segment inside every active square cell?

## Objects

- A square grid cell with four ordered sides.
- The four radial field values at its corners.
- The filtered list of threshold-crossing sides.
- Exact interpolation data on every selected side.

## Formal claims

- Every cell has 0, 2, or 4 crossing sides.
- Opposite-corner radial sums satisfy the parallelogram identity.
- Four-way alternating crossing is impossible.
- Every active cell therefore has exactly two crossing sides.
- These sides form the two vertices of one local contour segment.
- Reversing a shared edge preserves its exact interpolation coordinates.

## Verification rule

The main Lean module and a separate import audit must compile. The audit reconstructs the radial identity, the two-side theorem, the segment cardinality, and reverse-edge invariance. No `axiom`, `sorry`, or `admit` declaration is allowed.

## Verification result

- Lean 4.32.1 accepts the main module and the separate import audit.
- The source gap scan is clean.
- The radial parallelogram identity, exact two-side theorem, segment cardinality, and reverse-edge invariant report only `propext` and `Quot.sound`.

## Honest boundary

Proved: unique local segment incidence and orientation-independent edge gluing.

Not proved: global cycle decomposition, uniqueness of the radial cycle, outer-boundary exclusion, ambient planar metric, or Hausdorff convergence.

## Next step

IF-BS-12: prove the global degree-two condition and assemble the local segments into closed polygonal cycles.
