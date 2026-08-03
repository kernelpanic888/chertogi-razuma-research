# Passport: IF-BS-20D

## Name

Global coordinate marking and potential of one contour orbit.

## Formal chain

`local side mark <-> global coordinate edge mark`

`local xor zero -> ClosedOn`

`ClosedOn -> RectangularPotentialWitness`

## Main objects

- `HorizontalEdgeMarked`
- `VerticalEdgeMarked`
- `HorizontalCoordinateMarked`
- `VerticalCoordinateMarked`
- `orbitRectangularMarking`
- `orbitRectangularMarking_closed`
- `orbitPotential`

## Honest boundary

Global closure and the potential are the target of this step. Transport from
`CutAvoidingStep` to colour preservation and final separation remains open.

## Verification

- Main module: Lean 4.32.1 pass.
- Independent audit: Lean 4.32.1 pass.
- Source scan: no `axiom`, `sorry`, or `admit`.
- Reported dependencies: only `propext`, `Classical.choice`, and `Quot.sound`.

## Next point

IF-BS-20E: classify each `UnitAdjacent` step as a canonical horizontal or
vertical edge, prove every orbit-cut-avoiding step preserves `orbitPotential`,
and conclude `SeparatesSides`.
