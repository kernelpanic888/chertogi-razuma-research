# IF-BS-22E: one-sided Euclidean contour-to-circle bound

## Purpose

IF-BS-22D proves a squared radial corridor for every real point of every local contour segment. IF-BS-22E converts that scalar statement into an actual Euclidean witness on the target circle.

## Target geometry

The target circle is

`S = {Q in R^2 | ||Q||^2 = 2}`

with radius `sqrt(2)`. For a contour point `P`, Lean constructs a radial witness `Q(P)`:

- if `P` is nonzero, scale `P` to radius `sqrt(2)`;
- if `P` is zero, use the fixed circle point `(sqrt(2), 0)`.

The zero branch makes the construction total. Lean proves in both branches that `Q(P)` lies on `S`.

## Metric bridge

For a point inside the target circle,

`dist(P,Q(P)) = sqrt(2) - ||P||`.

The exact algebraic comparison is

`(sqrt(2) - ||P||)^2 <= 2 - ||P||^2`.

Combining this with IF-BS-22D gives, for every real `t in [0,1]` on every local segment,

`dist(P_m(t), Q_m(t)) <= sqrt(3) / m`.

The metric used here is the ordinary Euclidean distance

`dist(P,Q) = sqrt((Px-Qx)^2 + (Py-Qy)^2)`.

## Convergence

Lean proves the explicit statement

`forall epsilon > 0, exists N > 0, forall m >= N, sqrt(3)/m < epsilon`.

Thus every point of the polygonal contour has a target-circle witness at Euclidean distance tending uniformly to zero.

## Honest boundary

This proves the directed contour-to-circle estimate only. It does not prove that every target-circle point has a nearby contour point. Therefore full Hausdorff convergence is not yet claimed.
