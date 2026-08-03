# Passport: IF-BS-22B

## Name

Exact signed embedding of the interpolated radial crossing.

## Formal chain

`u = innerPoint(edge), v = outerPoint(edge)`

`d = F(v)-F(u) > 0, n = T-F(u), 0 <= n <= d`

`P(edge) = ((d-n)u + nv)/(dm)` in centered signed coordinates

`||P(edge)||^2 = 2 - n(d-n)/(d^2 m^2)`

## Main objects

- `centeredX`, `centeredY`
- `centered_square`, `centered_radius`
- `centered_unit_edge`
- `weighted_square_identity`
- `weighted_vector_square_identity`
- `SignedRationalPoint`
- `interpolatedSignedPoint`
- `interpolation_raw_radius_identity`
- `interpolation_squared_radius_deficit_exact`

## Claim boundary

The exact signed rational point and its exact squared radial deficit are
claimed. A segment-wide radial bound, reverse coverage of the continuous
circle, and a two-sided Hausdorff estimate are not claimed here.

## Verification

- Main module: Lean 4.32.1 pass.
- Independent audit: Lean 4.32.1 pass.
- Source scan contains no `axiom`, `sorry`, or `admit`.
- No new Mathlib algebra tactic is imported.
- Audited theorems report only `propext` and `Quot.sound`.

## Next point

IF-BS-22C: extend the endpoint identity to every rational point of each
polygonal contour segment and prove a uniform segment-wide radial bound.
