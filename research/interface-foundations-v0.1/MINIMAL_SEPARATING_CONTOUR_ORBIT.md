# IF-BS-20A: minimal separating contour orbit

## Stronger bond statement

Let `R` be any selected family of oriented threshold-crossing edges. A path
avoiding `R` may use all noncrossing unit edges and every crossing edge not in
`R`.

If deleting `R` separates every inside sample from every outside sample, then
`R` contains every threshold crossing:

`SeparatesSides(R) -> forall e, R(e)`.

The proof restores an omitted crossing `e`. IF-BS-18 connects any inside point
to the inside endpoint of `e` and its outside endpoint to any outside point.
The restored edge therefore contradicts separation.

## Link to IF-BS-15

Every IF-BS-15 contour state now has a proof-carrying oriented crossing edge.
`OrbitCut(O)` is the family of crossing edges represented by states in an orbit
predicate `O`.

Therefore, if one closed contour orbit is proved to separate the two sampled
regions, that orbit represents every threshold-crossing edge. No second
edge-disjoint separating contour can remain.

## Red boundary

The remaining fact is geometric, not graph-theoretic: prove that an IF-BS-15
closed medial orbit separates the rectangular grid. This is the finite digital
Jordan step. It has not been smuggled into the bond theorem.
