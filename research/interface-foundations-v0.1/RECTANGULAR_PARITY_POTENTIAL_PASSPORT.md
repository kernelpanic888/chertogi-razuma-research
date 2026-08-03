# Passport: IF-BS-20B

## Name

Finite rectangular parity potential.

## Formal chain

`even cell incidence -> Boolean vertex potential`

`marked edge -> opposite endpoint colours`

`colour-preserving path -> cannot cross marked edge`

## Main objects

- `RectangularEdgeMarking`
- `CellEven`
- `ClosedOn`
- `vertexPotential`
- `RectangularPotentialWitness`
- `closedMarking_hasPotential`
- `RelationReachable`
- `no_color_preserving_path_across`

## Claim boundary

The finite parity lemma is internal and does not invoke a continuous Jordan
curve theorem. Instantiation for an IF-BS-15 orbit remains the next theorem.

## Verification

- Main module: Lean 4.32.1 pass.
- Independent audit: Lean 4.32.1 pass.
- Source scan: no `axiom`, `sorry`, or `admit`.
- Boolean path preservation and marked-endpoint separation are axiom-free.
- The finite parity potential uses only `propext` and `Quot.sound`.

## Next point

IF-BS-20C: define the canonical edge marking of one successor orbit, prove
even incidence in every cell, and transport its Boolean potential to
`SeparatesSides (OrbitCut orbit)`.
