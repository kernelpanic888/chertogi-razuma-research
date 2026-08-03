# IF-BS-22F-F4: Composition of controlled chambers

## Result

Let `F : X -> Y` and `G : Y -> Z` be controlled homeomorphic coordinate
changes. Write their forward constants as `L_F,L_G` and their inverse constants
as `M_F,M_G`.

Lean now packages the sequential route `G after F` as another controlled
equivalence with

`L_(G after F) = L_G L_F`,

`M_(G after F) = M_F M_G`.

Composition acts pointwise as expected, the inverse traverses the two chambers
in reverse order, and threefold composition is associative both pointwise and
at the level of metric constants.

## Boundary consequence

For any computable boundary model with envelope `e_n`, the composed chamber
satisfies

`d_H((G after F)[K_n],(G after F)[I]) <= L_G L_F e_n`.

The transported interface remains the actual frontier of the transported
inside region, and its Hausdorff distance still tends to zero.

## Honest boundary

The theorem covers every fixed finite composition. Products can enlarge a
finite-resolution error even though convergence is preserved. Infinite chains
require a separate uniform product or summability condition and are not claimed
here.
