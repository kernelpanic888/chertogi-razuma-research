# Passport: IF-BS-20C

## Name

Zero-or-two local incidence for one alternating contour orbit.

## Formal chain

`orbit edge -> local mate edge -> second orbit edge`

`IF-BS-11 exactly two crossings -> zero or two orbit marks`

`zero or two marks -> xor around cell is zero`

## Main objects

- `SameContourOrbit`
- `EdgeMarkedByOrbit`
- `SideMarkedByOrbit`
- `edgeMarked_localMate`
- `cellSideMarks_zero_or_two`
- `cellSideMark_even`

## Honest boundary

Local parity is the target of this step. The global coordinate marking and
transport from its potential to the threshold cut remain IF-BS-20D.

## Verification

- Main module: Lean 4.32.1 pass.
- Independent audit: Lean 4.32.1 pass.
- Source scan: no `axiom`, `sorry`, or `admit`.
- Reported dependencies: only `propext`, `Classical.choice`, and `Quot.sound`.

## Next point

IF-BS-20D: define global horizontal/vertical orbit marks, prove agreement with
the four local side marks, obtain the potential from IF-BS-20B, and prove
`SeparatesSides` for the orbit cut.
