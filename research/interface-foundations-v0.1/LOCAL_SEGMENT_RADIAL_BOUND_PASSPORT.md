# Passport: IF-BS-22C

## Name

Uniform radial bound on every rational point of a local contour segment.

## Formal chain

`IF-BS-11 -> exactly two crossing sides per active cell`

`IF-BS-22B -> endpoint deficit <= 1/m^2`

`same cell -> endpoint separation^2 <= 2/m^2`

`P(k/r) = ((r-k)P0 + kP1)/r`

`2 - ||P(k/r)||^2 = R/(r^2 D^2 m^2)`

`0 <= R/(r^2 D^2 m^2) <= 3/m^2 -> 0`

## Main objects

- `uncenteredXNumerator`, `uncenteredYNumerator`
- `InCellCoordinates`
- `same_cell_common_separation_le`
- `common_centered_separation_exact`
- `segmentPoint`
- `segmentResidualNumerator`
- `segment_squared_radius_deficit_exact`
- `weighted_segment_residual_le_three`
- `segmentRadialResidual`
- `local_segment_every_rational_point_exact_and_bounded`
- `local_segment_radial_bound_limit`

## Claim boundary

The exact identity and the uniform `3/m^2` bound are claimed for every rational
parameter on every local contour segment. Extension to arbitrary real segment
parameters, reverse circle-to-contour coverage, and a two-sided Hausdorff
estimate are not claimed here.

## Verification

- Main module: passed with Lean 4.32.1.
- Independent audit: passed with Lean 4.32.1.
- Source scan: no `axiom`, `sorry`, or `admit` found.
- Audited theorem dependencies are limited to Lean's standard `propext`, `Quot.sound`, and, where finite segment vertices are selected, `Classical.choice`.
- No additional Mathlib geometry or algebra tactic is imported.

## Next point

IF-BS-22D: construct the real completion of the rational segment trace and
transport the uniform radial bound to every real point of every local segment.
