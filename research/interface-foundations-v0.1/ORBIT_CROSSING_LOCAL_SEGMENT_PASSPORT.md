# Passport: IF-BS-22F-B3C1

## Objective

Turn the sign-facing threshold crossing supplied by IF-BS-22F-B3A/B into a concrete local segment of the selected global contour orbit.

## Inputs

- IF-BS-11 active-cell local polygonal segments.
- IF-BS-20 state-to-oriented-crossing representation.
- IF-BS-21 global single-orbit membership.
- IF-BS-22F-B2 four exact axis crossings.
- IF-BS-22F-B3A/B inward coordinate rounding for arbitrary circle points.

## New objects

- `localSegmentOfState`
- `segmentVertexOfState`
- `segmentEdgeOfState`
- `OrbitLocalSegmentWitness`
- `signFacingCrossing`

## Proof obligations

- A contour state determines an active local cell.
- Its stored side is a vertex of that local segment.
- The interpolated edge's inner and outer samples agree with the represented oriented crossing.
- Sign selection chooses right for nonnegative target x and left for negative target x.
- The selected crossing remains in the global orbit and therefore has a local-segment witness.

## Red boundary

No reverse Euclidean distance estimate is claimed here. The target point and extracted segment have not yet been placed in one quantitative bound.

## Next point

IF-BS-22F-B3C2: use the inward rounding error, the fixed-row identity, adjacent threshold samples, and the segment interpolation to construct a point on the extracted segment within an explicit `O(1/m)` Euclidean distance of the target-circle point.
