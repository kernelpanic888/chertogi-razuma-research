# IF-BS-10: interpolated boundary contour

## Construction

Every adjacent grid edge whose endpoints lie on opposite sides of the radial threshold is oriented from its inside endpoint to its outside endpoint. If their field values are `F_in` and `F_out`, the exact linear crossing parameter is

`t = (T-F_in)/(F_out-F_in)`.

Lean proves `F_out-F_in > 0` and `0 <= t <= 1`. It also proves the denominator-cleared interpolation identity

`(F_out-F_in)F_in + (T-F_in)(F_out-F_in) = (F_out-F_in)T`.

Thus the point is not selected visually: it is the exact threshold point of the piecewise-linear field on the edge.

## Metric localization

At scale `m`, an edge has normalized arclength `1/m`. The two distances from the interpolated crossing to the edge endpoints are

`t/m` and `(1-t)/m`.

Both are proved to be at most `1/m`. Since the existing rational limit proves `1/m < epsilon` at sufficiently large `m`, the discrete crossing endpoints and their interpolated contour representatives converge in this explicit edge metric.

## Red boundary

This is a genuine metric statement along each crossing edge. It is not yet a theorem about Euclidean distance in the ambient plane, continuity between neighbouring edge crossings, topology of the assembled polygon, or planar Hausdorff distance to the smooth circle.

## Next

IF-BS-11 should assemble neighbouring interpolated crossings into a polygonal contour, prove local incidence, and then establish a two-sided planar distance bound.
