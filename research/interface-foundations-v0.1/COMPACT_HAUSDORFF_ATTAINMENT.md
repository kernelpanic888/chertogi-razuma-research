# IF-BS-22F-B3F: compact Hausdorff attainment

## Closed carriers

The canonical closed carriers are

`K_target := closure(targetCircleCarrier)`

`K_m := closure(contourCarrier(m))`.

Taking these closures does not alter Mathlib's Hausdorff distance.

## Compactness

Every target point has norm `sqrt(2)`, so `K_target` lies in the closed ball of radius `sqrt(2)`.

Every contour point is within `4/m` of a target point, so `K_m` lies in the closed ball of radius `sqrt(2)+4/m`.

Both carriers are closed and bounded in canonical Euclidean two-space; therefore both are compact.

## Attained converse

For two nonempty compact subsets of the ambient plane and any `r>=0`,

`hausdorffDist(A,B) <= r`

is equivalent to the two exact witness conditions

`forall a in A, exists b in B, dist(a,b) <= r`

and

`forall b in B, exists a in A, dist(b,a) <= r`.

Compactness is the missing condition: it makes each `infDist` attain an actual nearest point.

## Genuine limit

For any supplied sequence of contour anchors at resolutions `m=n+1`, the standard Hausdorff-distance sequence satisfies

`Filter.Tendsto d_H(K_(n+1), K_target) atTop (nhds 0)`.

This is the canonical topological limit statement, not only its epsilon paraphrase.

## Physical boundary

Compactness and Hausdorff convergence are mathematical properties of the constructed Euclidean carriers. They do not turn `1/m` into a physical Planck length or establish a minimum physical distance.
