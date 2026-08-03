# Passport: IF-BS-22A

## Name

Uniform quadratic residual of exact edge interpolation.

## Formal chain

`0 <= n <= d -> n(d-n) <= d^2`

`n(d-n)/(d^2 m^2) <= 1/m^2`

`1/m^2 -> 0`

## Main objects

- `squaredCellWidth`
- `curvatureResidual`
- `curvatureResidual_le_squaredCellWidth`
- `squared_cell_width_limit`
- `interpolated_curvature_residual_limit`
- `InterpolatedEdgeRefinementCertificate`

## Claim boundary

The exact rational algebraic residual and its rate are claimed. The embedded
planar identity, segment-wide bound, and two-sided Hausdorff estimate are not.

## Verification

- Main module: Lean 4.32.1 pass.
- Independent audit: Lean 4.32.1 pass.
- Source scan: no `axiom`, `sorry`, or `admit`.
- Core product bound is axiom-free.
- Uniform residual bound, limit, and certificate use only `propext` and
  `Quot.sound`.

## Next point

IF-BS-22B: define signed rational coordinates of every IF-BS-10 interpolation
point and prove that its squared radial deficit is exactly the curvature
residual defined here.
