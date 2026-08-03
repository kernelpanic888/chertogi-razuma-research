# IF-BS-22D: real completion of every local contour segment

## Purpose

IF-BS-22C controlled every rational point of a local polygonal contour segment. IF-BS-22D closes the missing analytic seam: the same segment is now parameterized directly by every real parameter `t` in the closed unit interval.

## Real trace

For the two exact IF-BS-10 crossing points `P0` and `P1`, define

`P(t) = (1 - t) P0 + t P1`, for `0 <= t <= 1`.

The two coordinate maps are continuous. If `t = k/r` comes from the old rational parameter type, the new real point is exactly the real cast of the old `segmentPoint`; the real trace is therefore an extension of the proved rational trace, not a replacement curve.

## Exact identity

Write

`delta_i = 2 - ||P_i||^2`

and

`S = ||P0 - P1||^2`.

Lean proves, for every real `t`,

`2 - ||P(t)||^2 = (1-t) delta_0 + t delta_1 + t(1-t) S`.

The IF-BS-22B endpoint identities and IF-BS-22C same-cell estimate give

`0 <= delta_0, delta_1 <= 1/m^2`,

`0 <= S <= 2/m^2`.

Consequently every point of every local segment satisfies

`0 <= 2 - ||P(t)||^2 <= 3/m^2`.

The constant is intentionally conservative. No optimization is needed for convergence.

## Vanishing corridor

Lean also proves the explicit epsilon statement

`forall epsilon > 0, exists N > 0, forall m >= N, 3/m^2 < epsilon`.

Thus the entire real polygonal trace, not merely its rational sample, lies in a radial squared-norm corridor whose width tends to zero.

## Honest boundary

This is a one-sided radial convergence statement. It does not yet prove Euclidean distance to the circle, reverse circle-to-contour coverage, or full Hausdorff convergence. Those are the next separate seams.
