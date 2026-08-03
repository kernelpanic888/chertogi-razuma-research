# IF-BS-22F-B3C2B1: dominant-coordinate metric prelude

## Verified analytic core

For every point `(x,y)` on `x^2+y^2=2`, at least one of `|x|` and `|y|` is at least one. The dominant-axis selector therefore always works with a radial coordinate bounded away from zero.

Inward rounding satisfies both:

`|round_m(u)| <= |u|`

`|u| - |round_m(u)| < 1/m`

For nonnegative dominant coordinate `a`, orthogonal coordinate `u`, inward-rounded coordinate `r`, and an adjacent radial threshold bracket `inside -> outside`, every affine interpolation parameter `t in [0,1]` obeys:

`|a - ((1-t) inside + t outside)| <= 3/m`.

## Meaning

The estimate is uniform at all four poles because the radial direction is selected only after comparing coordinate magnitudes. The former horizontal-only route lacked this uniformity.

## Honest boundary

This theorem is stated over real bracket data. The next adapter must prove that the finite-grid crossing and its interpolated local segment endpoint satisfy exactly these hypotheses.
