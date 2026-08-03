# Passport: IF-BS-13

## Name

Exact global degree two and zero mod-two boundary.

## Question

Are the two canonical neighbouring segments the only incidences at each exact contour vertex?

## Formal claims

- Undirected edge representation is explicit and orientation independent.
- Every horizontal incidence is above/south or below/north.
- Every vertical incidence is left/east or right/west.
- Both canonical incidences exist and are distinct.
- Every crossing vertex therefore has exactly two incidences.
- The complete family is packaged as a zero-boundary mod-two contour.

## Verification rule

The main Lean module and separate import audit must compile. The audit reconstructs both classification theorems, both exact-two certificates, and the global zero-boundary package. No `axiom`, `sorry`, or `admit` declaration is allowed.

## Verification result

- Lean 4.32.1 accepts the main module and the separate import audit.
- The source gap scan is clean.
- Both incidence classifiers, both `ExactlyTwo` certificates, and `ModTwoBoundaryZero` report only `propext`, `Classical.choice`, and `Quot.sound`.

## Honest boundary

Proved: exact combinatorial degree two and vanishing boundary coefficient modulo two at every crossing vertex.

Not proved: an explicit cycle traversal, connectedness, uniqueness of the radial cycle, simple embedding, planar Hausdorff convergence, or physical calibration.

## Next step

IF-BS-14: construct the finite successor permutation and extract the closed cycle orbits of the polygonal contour.
