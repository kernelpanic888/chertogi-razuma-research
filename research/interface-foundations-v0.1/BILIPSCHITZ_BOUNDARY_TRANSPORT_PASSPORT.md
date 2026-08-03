# Passport IF-BS-22F-F1

## Question

How much approximation error can a genuine shape deformation introduce?

## Input

- a `ComputableBoundaryModel X`;
- a homeomorphic equivalence `F : X <-> Y`;
- a forward Lipschitz constant `L`;
- an inverse Lipschitz constant `M`.

## Verified quantitative law

`d_H(F[K_n],F[I]) <= L * d_H(K_n,I) <= L * e_n`.

Since `e_n -> 0`, the transported family converges to the actual transported frontier.

## Honest limitation

No particular deformation is silently assumed. The theorem does not call an ellipse verified until its anisotropic map and both constants are supplied.

## NEXT_POINT

IF-BS-22F-F2: construct the explicit anisotropic Euclidean deformation `(x,y) -> (2x,y)`, prove forward constant `2` and inverse constant `1`, and instantiate a verified ellipse chamber.
