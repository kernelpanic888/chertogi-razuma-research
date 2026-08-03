# Passport: IF-BS-20E

## Name

Potential separation and completeness of one radial contour orbit.

## Formal chain

`orbit local parity -> global potential`

`avoiding step -> unmarked edge -> colour preserved`

`anchor crossing -> opposite colours`

`inside/outside connectivity -> global side separation`

`separating orbit cut -> complete threshold cut`

## Main theorems

- `unitAdjacent_has_canonical_edge`
- `markedUnitAdjacent_endpoints_differ`
- `unmarkedUnitAdjacent_preserves_color`
- `cutAvoidingStep_preserves_color`
- `orbitSides_have_different_colors`
- `contourOrbitCut_separates`
- `contourOrbitCut_is_full`

## Claim boundary

The finite radial geometric contour is the target. Continuous convergence and
identification with the exact Euclidean boundary remain separate obligations.

## Verification

- Main module: Lean 4.32.1 pass.
- Independent audit: Lean 4.32.1 pass.
- Source scan: no `axiom`, `sorry`, or `admit`.
- Unit-edge classification uses only `propext` and `Quot.sound`.
- Final separation and completeness report only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Next point

IF-BS-21: package IF-BS-10 through IF-BS-20E as the finite radial boundary
theorem, then formulate and prove a quantitative refinement/convergence bound.
