# Passport: IF-BS-22F-B3D

## Objective

Turn the two audited directed contour bounds into one common Hausdorff-style radius and prove epsilon convergence as resolution increases.

## Formal object

`HausdorffStyleApproximation m delta := BidirectionalCircleApproximation m delta delta`

`hausdorffEnvelope(m) := 4/m`

## Required claims

- `sqrt(3)/m <= 4/m` for `m > 0`.
- Both directed witness conditions hold with the common radius `4/m`.
- For every `epsilon > 0`, eventually `4/m < epsilon`.
- Therefore both directed witness conditions eventually hold with radius `epsilon`.

## Verification gate

- Main module compiles under Lean 4.32.1.
- Independent audit exposes theorem signatures and dependency axioms.
- No source `axiom`, `sorry`, or `admit`.

## Red boundary

`d_H*` is the explicit pointwise two-sided criterion for the model's own Euclidean distance. The theorem is mathematical convergence of a finite contour model, not an empirical Planck-scale measurement.

## Next point

Completed by IF-BS-22F-B3E in `StandardHausdorffMetricBridge.lean`: the constructive criterion implies Mathlib's standard Hausdorff bound through an injective Euclidean embedding and two explicitly nonempty carriers. A same-radius converse remains conditional on distance attainment.
