# IF-BS-22F-F2: Anisotropic ellipse chamber

## Result

The controlled transport layer now has a concrete non-circular instance.
On the Euclidean plane define

`F(x,y) = (2x,y)`, `F^-1(x,y) = (x/2,y)`.

Lean verifies that `F` is 2-Lipschitz and `F^-1` is 1-Lipschitz. Transporting
the audited radial interface `x^2+y^2=2` through `F` produces the exact boundary

`x^2/4 + y^2 = 2`.

This set is not a decorative ellipse. It is proved to be the actual frontier of
the transported inside region. Every compact computed carrier is transported
with the quantitative estimate

`d_H(F[K_n], F[I]) <= 2 e_n`,

and the resulting Hausdorff distance tends to zero.

## What this closes

- An explicit non-isometric homeomorphism is constructed.
- Both metric-control constants are supplied and checked.
- The target interface has a coordinate equation.
- The transported interface remains the actual topological frontier.
- The computable contour family converges to that frontier.

## Honest boundary

This is a theorem about Euclidean geometry, topology, and computable boundary
approximation. It does not identify the numerical resolution band with a
physical Planck scale and does not by itself establish a law of nature.
