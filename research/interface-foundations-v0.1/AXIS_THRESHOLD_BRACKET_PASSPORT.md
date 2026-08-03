# Passport IF-BS-22F-B1

## Name

Finite row scan and threshold bracket.

## Inputs

- Uniform `4m+1` radial grid.
- A row whose central sample is inside.
- IF-BS-21 completeness of the unique contour orbit.

## Outputs

- Least outside rightward scan offset.
- Adjacent inside/outside pair.
- An oriented radial threshold crossing on the selected row.
- Proof that this crossing belongs to the global contour orbit.

## Verification

- Main module: passed with Lean 4.32.1 without warnings.
- Independent audit: passed with Lean 4.32.1.
- Source scan: no `axiom`, `sorry`, or `admit` found.
- Audited theorem dependencies are standard `propext`, `Quot.sound`, and `Classical.choice` for least-witness selection and orbit packaging.

## Red boundary

- Only the rightward row scan is constructed here.
- The four-direction symmetry layer remains separate.
- Rounding a real circle coordinate to a safe row/column remains open.
- No reverse mesh-width estimate is claimed yet.

## Next point

IF-BS-22F-B2: prove reflection and coordinate-swap invariance, producing left, top, and bottom threshold brackets from B1.
