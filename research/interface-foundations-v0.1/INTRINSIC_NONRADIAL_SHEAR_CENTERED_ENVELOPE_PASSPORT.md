# Passport / IF-BS-22F-F8C24

## Identity

- Route: `IF-BS-22F-F8C24`
- Name: `Centered two-point envelope`
- State: `FORMALLY VERIFIED / EXACT SCALAR OPTIMUM`
- Parent: `IF-BS-22F-F8C23`

## Inputs

- Exact local tangent envelope `E(a)` and its attained maximizer.
- First-quadrant unit coordinates `(X,Y)`.
- Center/half-chord radii `(r,k)` with `r^2+k^2=1`.
- Two absolute-value midpoint identities represented by two `max` branches.

## New definitions

- `centeredTwoPointEnvelope(a,X,Y,r,k)`.
- `CenteredEnvelopeValues(a)`.

## Verified outputs

- `r+k<=sqrt(2)` for the radial unit pair.
- Exact bounds for both mixed branches.
- `centeredTwoPointEnvelope<=E(a)` in all four max regimes.
- Attainment at `r=1`, `k=0` and `tangentEnvelopePoint(a)`.
- `E(a)` is `IsGreatest` for the complete centered value set.
- Main/audit use no local `axiom`, `sorry`, or `admit`.
- Audit dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

## Interpretation

The coarse F8C23 gap disappears in the exact centered scalar chamber. This is not yet the final global pairwise theorem because actual-pair transport remains to be proved.

## Red boundary

Construct and verify the canonical centered record of every pair in `directionalDiamondBand`, including the antipodal midpoint-zero branch.

## Next point

`IF-BS-22F-F8C25`: actual-pair centered extraction, antipodal split, and the global equality between the least chord modulus and `exactLocalTangentModulus`.

