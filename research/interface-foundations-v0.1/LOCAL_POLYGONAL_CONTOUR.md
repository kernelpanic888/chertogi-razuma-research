# IF-BS-11: local polygonal contour

## Construction

Each square cell is traversed counterclockwise through its south, east, north, and west sides. A side is selected exactly when its two endpoint predicates disagree. The selected sides carry the exact IF-BS-10 interpolation points.

## Why there is one segment

A cyclic binary boundary has an even number of changes, so a cell can initially have 0, 2, or 4 crossing sides. The radial field satisfies the exact cell identity

`F(SW) + F(NE) = F(SE) + F(NW)`.

Four crossings would require one diagonal pair to be at or below the threshold and the other diagonal pair to be strictly above it. Their sums would then be unequal, contradicting the identity. Therefore an active radial cell has exactly two crossing sides.

Those two exact crossing points define one unambiguous local polygonal segment. The four-way marching-squares saddle case cannot occur for this sampled radial field.

## Gluing rule

Neighbouring cells traverse a shared side in opposite directions. Lean proves that reversing a crossing edge preserves its inside endpoint, outside endpoint, interpolation numerator, and interpolation denominator. The two cells therefore name the same exact contour point on their shared side.

## Red boundary

This proves local two-vertex incidence and orientation-independent gluing data. It does not yet prove that all active cells form one global cycle, exclude contact with the outer grid boundary, or establish a planar Hausdorff estimate.

## Next

IF-BS-12 should prove that no contour edge lies on the outer grid boundary, give every local vertex degree two globally, and assemble the segments into closed cycles.
