# IF-BS-22A: interpolated curvature residual

## Exact rational correction

For an IF-BS-10 crossing edge, write the interpolation parameter as `n/d`.
The quadratic correction between endpoint-linear interpolation and the actual
square along a unit edge is represented without floating point by

`n(d-n) / (d^2 m^2)`.

The numerator is nonnegative because `0 <= n <= d`.

## Uniform bound

`n(d-n) <= d^2`, hence

`curvatureResidual(edge) <= 1/m^2`.

The bound tends to zero for every positive rational epsilon. Together with the
existing IF-BS-10 endpoint arclength bounds, this yields a uniform refinement
certificate for every crossing edge.

## Red boundary

This module proves the algebraic correction and its rate. It does not yet
identify the correction with the squared radial residual of an explicitly
embedded rational point, extend it over full cell segments, or prove reverse
coverage of the continuous circle. Those are required before using the word
Hausdorff for the final theorem.
