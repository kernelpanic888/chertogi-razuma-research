# IF-BS-15: concrete radial contour traversal

## Concrete state

A contour state is a concrete pair `(cell, side)` together with a proof that the side crosses the radial threshold. It is therefore an actual incidence of the IF-BS-11 polygonal contour, not an abstract graph vertex.

## Two moves

The local mate is the unique other crossing side of the same active cell. The shared mate is the unique other cell-side representation of the same global crossing edge. IF-BS-11 supplies the first exact-two certificate; IF-BS-13 supplies the second.

Both partner relations are symmetric and irreflexive. Choosing their unique partners therefore gives two fixed-point-free involutions. Their alternating successor is exactly the traversal kernel proved in IF-BS-14.

## Finite closure

All bounded grid cells and all four sides are explicitly enumerated. Filtering this finite list by the verified crossing predicate gives a list covering every concrete contour state. Applying IF-BS-14 yields a strictly positive period for every state.

## Verification

The main module and the independent audit compile with Lean 4.32.1. The source-gap scan is empty. The constructive local uniqueness and finite-cover results use only `propext` and `Quot.sound`; selecting the unique mates and the final closed-cycle theorem additionally use `Classical.choice`.

## Red boundary

This establishes finite combinatorial closure for every component of the sampled radial contour. It does not yet prove that all states belong to one cycle, identify which cycle approximates the intended continuum circle, or establish a Hausdorff convergence rate as the grid is refined.

## Next

IF-BS-16 should identify the radial component and prove that the concrete traversal has one cycle rather than an unspecified finite family of cycles.
