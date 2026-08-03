# Passport / IF-BS-22F-F8C23

## Identity

- Route: `IF-BS-22F-F8C23`
- Name: `Intrinsic nonradial shear finite-chord bridge`
- State: `FORMALLY VERIFIED / GLOBAL SUFFICIENT MODULUS`
- Parent: `IF-BS-22F-F8C22`

## Inputs

- Exact realizable diamond `directionalDiamondBand`.
- Unit direction identity and exact slope-width bound.
- Product-metric coordinate bounds for `Delta y` and `Delta s`.
- Exact local tangent modulus `L_tan(a)` from F8C21-F8C22.

## New definitions

- `chordBridgeModulus(a) = 2a(sqrt(2)+1)+2sqrt(2)a^2`.
- `chordBridgeGap(a) = chordBridgeModulus(a)-exactLocalTangentModulus(a)`.

## Verified outputs

- Exact finite-difference normal form for `forwardBlowUpSq` on the diamond.
- Global pairwise bound for every finite pair in the exact realizable diamond.
- `exactLocalTangentModulus(a) <= chordBridgeModulus(a)` for `a>=0`.
- `chordBridgeGap(a)>=0` for `a>=0`.
- At `a=1/2`, `chordBridgeModulus=1+(3/2)sqrt(2)`.
- Independent audit uses only `propext`, `Classical.choice`, and `Quot.sound`.
- No local `axiom`, `sorry`, or `admit`.

## Public reading

- Mint: exact finite-difference identity.
- Cyan: global pairwise inequality.
- Gold: local-to-chord comparison and half-amplitude readout.
- Red: least global modulus is not yet identified.

## Red boundary

The certificate is sufficient but not proved optimal. F8C23 does not identify the infimum of all global chord moduli and does not claim equality with the local tangent modulus.

## Next point

`IF-BS-22F-F8C24`: optimize the centered two-point problem on the compact midpoint/chord chamber and decide whether the certified gap is genuine or removable.

