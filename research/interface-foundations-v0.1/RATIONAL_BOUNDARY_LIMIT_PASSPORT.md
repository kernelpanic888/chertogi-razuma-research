# Passport IF-BS-06

Date: 2026-07-31
Object: rational metric embedding and standard epsilon-N contraction.

## Inputs

- Mesh node i of G_n.
- Rational embedding i/n into [0,1].
- PlanckTouch endpoints k and k+1.
- Positive rational tolerance epsilon=p/q.
- Fraction order by positive-denominator cross multiplication.

## Checked outputs

1. Every embedded mesh node lies in the rational unit interval.
2. Boundary endpoint numerators are k and k+1.
3. Their numerator gap is exactly one.
4. Cell width is the positive fraction 1/n.
5. 1/n < p/q is equivalent to q < p*n.
6. N=q+1 is a valid witness for every positive rational epsilon=p/q.
7. For all n>=N, the persistent boundary band is narrower than epsilon.

## Claim boundary

The theorem quantifies over positive rational tolerances. It does not yet carry
a real metric-space embedding or a physical calibration to Planck length.

## Next slice

Build a two-dimensional finite grid with a declared scalar field. Compute a
curved threshold contour, prove every reported boundary cell crosses the level,
and test refinement stability of the contour under a grid coarsening map.
