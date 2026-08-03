# Passport IF-BS-22F-E

## Question

Can the verified boundary model be moved into another metric chamber without redoing the proof?

## Input

- a `ComputableBoundaryModel X`;
- an isometric equivalence `F : X ≃ᵢ Y`.

## Verified transport

- `A' = F[A]`;
- `I' = F[I]`;
- `E' = F[E]`;
- `K'_n = F[K_n]`;
- `frontier(A') = I'`;
- `d_H(K'_n,I') = d_H(K_n,I)`;
- `d_H(K'_n,frontier(A')) -> 0`.

## Honest limitation

The theorem relocates the chamber without changing its intrinsic metric shape. It does not yet create a noncircular interface from the radial witness.

## NEXT_POINT

IF-BS-22F-F: define a controlled bi-Lipschitz boundary transport and prove the quantitative envelope `d_H(F[K_n],F[I]) <= L * e_n`, enabling verified noncircular chambers.
