# Passport: IF-BS-17

## Name

Radial exterior outward-connectivity carrier.

## Question

Can every sampled outside point reach the same outer-frame point without entering the sampled disk?

## Objects

- A deterministic outward x-coordinate.
- A vertical frame point and bottom-frame point.
- Horizontal and vertical outside-segment predicates.
- The common frame corner `(0,0)`.
- A three-segment exterior path certificate.

## Formal claims

- Radial x-offset never decreases on the selected outward segment.
- The outward horizontal segment remains outside.
- Both outer-frame segments remain outside.
- Every outside sample reaches the common frame corner through three certified segments.

## Verification rule

The main Lean module and independent import audit must compile. The audit reconstructs outward monotonicity and the complete three-segment path. No `axiom`, `sorry`, or `admit` declaration is allowed.

## Verification result

Passed with Lean 4.32.1. The main module and independent audit compile, and the source-gap scan is empty. The final common-frame-corner theorem uses only `propext` and `Quot.sound`.

## Honest boundary

Proved here: orthogonal connectivity of every sampled exterior point to one common frame corner.

Not proved here: the finite planar separation bridge or uniqueness of the concrete contour cycle.

## Next step

IF-BS-18: finite planar separation and one-cycle uniqueness.
