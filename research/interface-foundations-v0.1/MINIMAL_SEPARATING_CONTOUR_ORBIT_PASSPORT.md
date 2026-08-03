# Passport: IF-BS-20A

## Name

Inclusion-minimal threshold cut and contour-orbit criterion.

## Proved chain

`omitted crossing -> restored bridge path -> failure of separation`

`separating subcut -> complete threshold cut`

`separating contour orbit -> orbit represents every crossing edge`

## Formal artifacts

- `CutAvoidingStep`
- `SeparatesSides`
- `separating_subcut_contains_every_crossing`
- `radialThresholdCut_isInclusionMinimal`
- `contourStateBridge`
- `contourStateBridge_spec`
- `OrbitCut`
- `separating_contour_orbit_contains_every_crossing`

## Honest boundary

The primal minimality theorem and state-to-edge map are proved. The digital
Jordan theorem saying that each closed medial orbit separates remains open.

## Verification

- Main module: Lean 4.32.1 pass.
- Independent audit: Lean 4.32.1 pass.
- Source scan: no `axiom`, `sorry`, or `admit`.
- Full-cut separation is axiom-free.
- Minimality and contour-state transport report only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Next point

IF-BS-20B: formalize finite rectangular digital Jordan separation for one
closed IF-BS-15 medial orbit. Minimality will then force that orbit to contain
the complete threshold boundary.
