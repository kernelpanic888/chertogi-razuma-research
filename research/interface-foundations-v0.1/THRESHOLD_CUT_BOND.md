# IF-BS-19: the threshold cut is a bond

## Complete cut

A noncrossing step is a unit-adjacent edge whose endpoints are both inside or both outside. Every finite path made only of such steps preserves its side. Therefore deleting all threshold-crossing edges separates every inside sample from every outside sample.

## Minimality

Each crossing edge has a canonical orientation from its inside endpoint to its outside endpoint. If any one such edge is restored, IF-BS-18 connects an arbitrary inside start to its inside endpoint and connects its outside endpoint to an arbitrary outside finish. The restored edge joins those two paths.

Thus every crossing edge is essential: removing the complete crossing set disconnects the sides, while restoring any one member reconnects them. This is the graph-theoretic bond certificate.

## Red boundary

No planar conclusion is hidden here. The verified result says that the primal threshold cut is a bond. The remaining theorem must use the rectangular embedding to prove that the corresponding medial or dual edge set is one cycle, then identify that cycle with the IF-BS-15 successor orbit.

## Next

IF-BS-20 should formalize finite rectangular-grid duality: a primal bond induces a connected degree-two medial contour.
