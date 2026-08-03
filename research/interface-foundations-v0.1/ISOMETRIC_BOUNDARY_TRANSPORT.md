# IF-BS-22F-E: Isometric boundary transport

## Result

An isometric equivalence transports the whole computable boundary model without loss.

For an isometry equivalence `F : X ≃ᵢ Y`, every region is transported by image:

`F[A]`, `F[I]`, `F[E]`.

The theorem proves:

- properness is preserved;
- the three side labels remain pairwise disjoint and exhaustive;
- `frontier(F[A]) = F[frontier(A)]`;
- compactness and nonemptiness of every carrier are preserved;
- `d_H(F[K_n], F[I]) = d_H(K_n, I)`;
- therefore `d_H(F[K_n], frontier(F[A])) -> 0`.

## Exact scope

This is lossless transport. An isometry can translate, rotate, reflect, or change coordinates, but it cannot deform a circle into a genuinely noncircular chamber.

## Red boundary

A noncircular deformation requires controlled distortion, not an isometry. The next formal layer must quantify how a bi-Lipschitz constant changes the Hausdorff envelope.
