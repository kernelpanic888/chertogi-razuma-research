# IF-BS-22F-A: reverse-coverage metric adapter

## Purpose

IF-BS-22E proves the directed contour-to-circle estimate. Reverse coverage needs one additional geometric input: the radial witnesses of the finite contour must form a quantitative mesh of the target circle. IF-BS-22F-A isolates that exact obligation and proves everything that follows from it.

## Native Euclidean metric

The module proves from coordinates:

- nonnegativity and symmetry of the distance;
- planar Cauchy-Schwarz;
- the two-dimensional norm triangle inequality;
- the Euclidean triangle inequality for `RealPlanePoint`.

No external metric identification is assumed.

## Mesh certificate

`ReverseCoverageMesh m delta` means:

for every target point `Q` on `x^2+y^2=2`, there is a real point `P_m(t)` on a local contour segment whose radial circle witness `R_m(t)` satisfies

`dist(Q,R_m(t)) <= delta`.

This is now the precise combinatorial-geometric target for the finite orbit.

## Reverse metric theorem

IF-BS-22E gives

`dist(R_m(t),P_m(t)) <= sqrt(3)/m`.

The triangle inequality therefore yields

`dist(Q,P_m(t)) <= delta + sqrt(3)/m`.

Lean packages this as `ReverseCoverageWitness` and combines it with the already proved forward direction in `BidirectionalCircleApproximation`.

## Honest boundary

This module does not manufacture `ReverseCoverageMesh`. The remaining theorem must construct it from threshold edges and IF-BS-21 orbit completeness. Until then, full Hausdorff convergence remains conditional on the mesh certificate.
