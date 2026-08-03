# IF-BS-22B: signed rational interpolation coordinates

## Result

Every exact IF-BS-10 crossing point now has an explicit signed rational
embedding in the physical plane.

For a scale `m`, let

`u = innerPoint(edge)`, `v = outerPoint(edge)`,

`d = F(v) - F(u) > 0`, and `n = T - F(u)` with `0 <= n <= d`, where
`F(p)` is the integer radial numerator and `T = 2m^2`.

The centered integer coordinates are

`sx(p) = p.x - 2m`, `sy(p) = p.y - 2m`.

The interpolated physical point is represented without division by

`X = (d-n)sx(u) + n sx(v)`,

`Y = (d-n)sy(u) + n sy(v)`,

with common denominator `dm`.

Lean proves the exact identity

`X^2 + Y^2 + n(d-n) = 2(dm)^2`.

Therefore the squared physical radius of the interpolated crossing is exactly

`2 - n(d-n)/(d^2 m^2)`.

The correction on the right is precisely the curvature residual introduced in
IF-BS-22A. It is no longer merely an algebraic candidate: it is the exact
squared radial deficit of the embedded IF-BS-10 point.

## Formal mechanism

- `centered_square` identifies signed-coordinate squares with the unsigned
  `natDistance` squares used by the earlier radial model.
- `centered_unit_edge` proves that every oriented grid edge has exact squared
  length one in centered integer coordinates.
- `weighted_vector_square_identity` is the two-dimensional chord identity.
- `interpolation_raw_radius_identity` connects that identity to the IF-BS-10
  threshold interpolation.
- `interpolation_squared_radius_deficit_exact` rewrites the target numerator as
  the radius-two circle numerator over the denominator `dm`.

The polynomial normalization is proved in the existing minimal Lean
foundation. No additional Mathlib algebra tactic is imported.

## Honest boundary

This result concerns the exact threshold point selected on every crossing edge.
It does not yet bound every point of the polygonal segment joining neighboring
crossings, and it does not prove reverse coverage from every point of the
continuous circle to the polygonal contour. Consequently a two-sided
Hausdorff-distance theorem is still open.
