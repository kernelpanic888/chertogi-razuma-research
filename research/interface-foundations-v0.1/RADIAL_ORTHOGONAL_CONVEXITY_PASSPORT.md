# Passport: IF-BS-16

## Name

Radial orthogonal-convexity and centre-connection carrier.

## Question

Can the sampled radial inside region split or contain a gap along a grid row or column?

## Objects

- Integer betweenness on one coordinate.
- Coordinate offsets from the exact centre.
- Horizontal and vertical inside segments.
- The exact centre sample.
- A two-segment inside path certificate.

## Formal claims

- The radial numerator is monotone in both offsets.
- Inside membership is downward closed in the offset order.
- Outside membership is upward closed in the offset order.
- Every row and column slice is interval-closed.
- Every inside sample has an L-shaped inside connection to the centre.

## Verification rule

The main Lean module and independent import audit must compile. The audit reconstructs monotonicity, interval closure, and the centre-connection theorem. No `axiom`, `sorry`, or `admit` declaration is allowed.

## Verification result

Passed with Lean 4.32.1. The main module and independent audit compile, and the source-gap scan is empty. Monotonicity is axiom-free; the final orthogonal star-connection theorem uses only `propext` and `Quot.sound`.

## Honest boundary

Proved here: orthogonal star-connectedness of the sampled inside region.

Not proved here: exterior connectivity, the finite planar separation theorem, or uniqueness of the boundary cycle.

## Next step

IF-BS-17: exterior outward connectivity and the one-cycle separation bridge.
