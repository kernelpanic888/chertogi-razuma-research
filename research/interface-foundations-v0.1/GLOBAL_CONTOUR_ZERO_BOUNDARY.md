# IF-BS-13: exact degree two and zero boundary

## Classification

A cell side represents a canonical grid edge when its ordered endpoints equal the canonical endpoints either directly or in reverse. Lean exhausts all four side orientations.

For a crossing horizontal edge, every representation is exactly one of:

- the south side of the cell above;
- the north side of the cell below.

For a crossing vertical edge, every representation is exactly one of:

- the east side of the cell to the left;
- the west side of the cell to the right.

The two canonical representations are distinct, both exist, and the classification proves that no third representation exists.

## Global statement

Every exact crossing vertex of the polygonal contour has degree exactly two. Over coefficients modulo two, its boundary coefficient is

`2 mod 2 = 0`.

The family of all horizontal and vertical crossing vertices is packaged as `ModTwoBoundaryZero`: the complete finite polygonal chain has no endpoint in the combinatorial mod-two sense.

## Red boundary

Zero mod-two boundary proves closure as a 1-cycle, not that the support is one connected component. A finite degree-two graph is a disjoint union of cycles, but the explicit finite traversal and uniqueness of the radial component are not yet formalized here.

## Next

IF-BS-14 should build a finite successor permutation on exact contour vertices, extract its cycle orbits, and then prove whether the radial contour has one component.
