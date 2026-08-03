# IF-BS-09: uniform radial boundary family

## Result

The fixed 17x17 computation from IF-BS-08 is now one member, `m = 4`, of a family of `(4m+1) x (4m+1)` radial grids. Grid coordinates are integer numerators at physical spacing `1/m`; the centre is `(2m,2m)` and the sampled squared-radius threshold is `2m^2`.

For every positive scale `m`, one horizontal or vertical grid step changes the radial numerator by at most

`J(m) = 4m + 1 <= 5m`.

Therefore both endpoints of every edge crossing the threshold lie in the exact field band

`|F_m(p) - 2m^2| <= 5m`.

After division by `m^2`, the squared-radius residual is at most `5/m`. For every positive rational `epsilon`, the Lean theorem constructs a scale `N` such that `m >= N` implies `5/m < epsilon`.

## Connection to IF-BS-08

At `m = 4`, the side length is exactly 17. The general radial numerator is definitionally equal to the quarter-step numerator already used by IF-BS-08, so the previous exhaustive chamber is preserved as a checked instance of the family.

## Red boundary

This proves uniform convergence of a squared-radius field residual for crossing-edge endpoints. It does not yet prove Hausdorff convergence of an interpolated polygonal contour to the Euclidean circle, nor any physical Planck-scale claim.

## Files

- `formal/UniformRadialBoundaryFamily.lean`: general family and uniform estimate.
- `formal/UniformRadialBoundaryFamilyAudit.lean`: independently reconstructed public claims and axiom report.

## Next

IF-BS-10 should convert the squared-radius residual into a metric radial bound and then state an honest Hausdorff-style theorem for an explicitly defined interpolated contour.
