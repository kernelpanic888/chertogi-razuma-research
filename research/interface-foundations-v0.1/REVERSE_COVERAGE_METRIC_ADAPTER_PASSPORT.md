# Passport IF-BS-22F-A

## Name

Metric adapter from a circle-witness mesh to reverse contour coverage.

## Inputs

- IF-BS-22E explicit radial witness and forward bound `sqrt(3)/m`.
- A finite-orbit mesh certificate `ReverseCoverageMesh m delta`.

## Outputs

- Coordinate-level proof of the Euclidean triangle inequality.
- Reverse bound `delta + sqrt(3)/m`.
- A bidirectional circle-approximation certificate with explicit forward and reverse bounds.

## Verification

- Main module: passed with Lean 4.32.1 without warnings.
- Independent audit: passed with Lean 4.32.1.
- Source scan: no `axiom`, `sorry`, or `admit` found.
- Audited theorem dependencies are exactly the standard `propext`, `Classical.choice`, and `Quot.sound`.

## Red boundary

- `ReverseCoverageMesh` is an explicit hypothesis, not yet a theorem.
- IF-BS-22F-B must construct this mesh from the radial threshold cut.
- Full Hausdorff convergence is still not claimed.

## Next point

IF-BS-22F-B: for every point of the target circle, construct a nearby radial threshold crossing and place it in the unique global orbit using IF-BS-21.
