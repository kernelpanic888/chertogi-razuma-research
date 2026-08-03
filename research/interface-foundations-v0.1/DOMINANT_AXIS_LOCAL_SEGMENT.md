# IF-BS-22F-B3C2A: dominant-axis local segment

## Why the selector changes

A horizontal-only construction is not uniformly stable near the upper and lower poles of the target circle. Rounding y inward by less than `1/m` can move the horizontal circle intersection by order `1/sqrt(m)` when x is near zero. Therefore it cannot support a uniform `O(1/m)` reverse-distance claim.

## Corrected route

- If `|x(q)| >= |y(q)|`, round y inward and select the right or left crossing by the sign of x.
- If `|y(q)| > |x(q)|`, swap the target coordinates, round x inward, and select the top or bottom crossing by the sign of y.

The selected radial coordinate is always the dominant coordinate. On the circle `x^2+y^2=2`, its absolute value is at least one, avoiding the pole singularity in the next metric estimate.

## Verified result

Both axis families exist on the same selected global contour orbit. The dominant-axis selector preserves that membership, and IF-BS-22F-B3C1 extracts a concrete local contour segment for the selected crossing.

## Honest boundary

The explicit Euclidean estimate is not yet claimed. The next theorem must convert dominant-coordinate stability, inward rounding, and crossing interpolation into a numerical constant `C` in `d(q,Gamma_m) <= C/m`.
