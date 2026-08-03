# Passport IF-BS-22F-B2

## Name

Exact axis symmetries for finite threshold crossings.

## Inputs

- The uniform `4m+1` radial grid.
- The B1 rightward least-outside threshold bracket.
- IF-BS-21 completeness of the global contour orbit.

## Outputs

- Vertical-centre reflection `R_x(x,y)=(4m-x,y)`.
- Coordinate exchange `S(x,y)=(y,x)`.
- Involution laws for both maps.
- Preservation of radial numerator, `Inside`, and unit adjacency.
- Transport of oriented threshold crossings.
- Right, left, top, and bottom crossings from one B1 bracket.
- Membership of all four crossings in the same complete global contour orbit.

## Verification

- Main verification target: `formal/AxisThresholdSymmetry.lean` under Lean 4.32.1.
- Independent audit target: `formal/AxisThresholdSymmetryAudit.lean`.
- Source gate: no declaration using `axiom`, `sorry`, or `admit` is permitted.

## Red boundary

- The four axial crossings do not yet constitute a full angular mesh.
- A real target-circle point has not yet been rounded to a safe discrete row or column.
- No reverse Euclidean distance estimate is claimed in B2.
- The finite contour is still a computable approximation, not an identification with a physical boundary.

## Next point

IF-BS-22F-B3: construct a safe row/column selector for an arbitrary target-circle point and derive a quantitative reverse-coverage estimate from the corresponding axial threshold bracket.
