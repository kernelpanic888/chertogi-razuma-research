# IF-BS-22F-F3: Positive diagonal ellipse family

## Result

For every pair of positive real parameters `a,b`, the map

`F_(a,b)(x,y) = (a x,b y)`

is packaged as a controlled homeomorphic coordinate change. Lean verifies

`||F(p)-F(q)|| <= max(a,b)||p-q||`

and

`||F^-1(p)-F^-1(q)|| <= max(a^-1,b^-1)||p-q||`.

The circle `x^2+y^2=2` is transported to the exact ellipse

`x^2/a^2 + y^2/b^2 = 2`.

The equation describes the actual topological frontier of the transported
inside region. If the original compact carriers have error envelope `e_n`, then

`d_H(F[K_n],F[I]) <= max(a,b)e_n`,

and this Hausdorff distance tends to zero.

## Meaning

The former `(2x,y)` example is one point in a verified two-parameter chamber
space. Circular, horizontally stretched, vertically stretched, and uniformly
scaled interfaces are now handled by one theorem.

## Honest boundary

Positivity of `a,b` is essential to the present orientation-preserving family.
The result is geometric and topological. No physical law or Planck-scale
identification follows from the deformation alone.
