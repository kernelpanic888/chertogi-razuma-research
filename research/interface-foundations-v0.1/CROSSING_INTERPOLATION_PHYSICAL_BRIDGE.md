# IF-BS-22F-B3C2B2B: crossing interpolation physical bridge

## Identity

The exact threshold point on a crossing edge has two constructions:

- affine interpolation of the normalized inner and outer grid samples using the IF-BS-10 interpolation parameter;
- the common-denominator real endpoint used by the local segment in IF-BS-22C/D.

The two constructions are exactly equal, coordinate by coordinate.

For any local segment vertex `v`:

`segmentRealPoint(0, segment, v, v) = edgePhysicalInterpolation(segmentEdge(segment,v))`.

Thus the selected crossing point is not merely near the contour: it is literally an endpoint admitted by the contour's real-segment representation.

## Honest boundary

The remaining theorem must instantiate the dominant bracket inequality in the horizontal and vertical branches and combine the two coordinate bounds into Euclidean distance.
