# Passport: IF-BS-10

## Name

Exact edge interpolation and metric localization.

## Question

Can every digital threshold crossing be turned into an exact contour point rather than an arbitrary marked pixel?

## Input

- The IF-BS-09 family at scale `m>0`.
- A unit-adjacent edge whose endpoint predicates cross the radial threshold.

## Construction

- Orient the edge from the inside endpoint to the outside endpoint.
- Set `d = F_out-F_in` and `n = T-F_in`.
- Use the exact parameter `t=n/d`.
- Measure distance by normalized arclength along the edge.

## Formal claims

- `d>0`.
- `n<=d`, hence `0<=t<=1`.
- Linear interpolation at `t` equals the threshold exactly.
- Endpoint distances are `t/m` and `(1-t)/m`.
- Both distances are at most one cell width `1/m`.
- For every positive rational epsilon, the common cell-width bound is eventually below epsilon.

## Verification rule

The main Lean module and a separate import audit must compile. The audit reconstructs the interpolation identity, both metric bounds, and the limit statement. The source must contain no `axiom`, `sorry`, or `admit` declarations.

## Verification result

- Lean 4.32.1 accepts the main module and the separate import audit.
- The source gap scan is clean.
- The exact interpolation identity, both endpoint bounds, and the mesh-limit theorem report only `propext` and `Quot.sound`.
- Edge orientation is computed directly from the natural-number threshold comparison; it does not use hidden classical choice.

## Honest boundary

Proved: exact piecewise-linear field crossing and a shrinking edge-arclength correspondence.

Not proved: planar polygon assembly, manifold structure, Euclidean nearest-point distance, Hausdorff convergence to the smooth circle, or physical calibration.

## Next step

IF-BS-11: assemble local crossings into a polygonal contour and prove a two-sided planar localization theorem.
