# IF-BS-22F-F1: Controlled bi-Lipschitz boundary transport

## Result

A controlled homeomorphic deformation may change the chamber's shape while preserving the full boundary architecture.

For `F : X -> Y` with forward Lipschitz constant `L` and a Lipschitz inverse:

- `frontier(F[A]) = F[frontier(A)]`;
- the three side labels remain pairwise disjoint and exhaustive;
- compact nonempty carriers remain compact and nonempty;
- `d_H(F[K_n],F[I]) <= L * d_H(K_n,I)`;
- if `d_H(K_n,I) <= e_n` and `e_n -> 0`, then
  `d_H(F[K_n],frontier(F[A])) -> 0`.

## Why both directions are recorded

The forward Lipschitz constant controls approximation error. The inverse Lipschitz constant records that the deformation is quantitatively reversible and cannot collapse distinct geometry into one point.

## Red boundary

The theorem is general and conditional. A specific noncircular chamber still requires an explicit controlled equivalence and verified constants.
