# Passport IF-BS-22F-D

## Question

Which assumptions survive after removing the circular geometry from IF-BS-22F-C?

## Formal objects

- `SideLabelInvariant inside interface outside`
- `BoundaryModel X`
- `InterfaceApproximation target`
- `ComputableBoundaryModel X`

## Required obligations

- the inside is proper;
- the interface is nonempty and is the actual frontier;
- inside, interface, and outside are pairwise disjoint and exhaustive;
- target and computable carriers are nonempty and compact;
- every Hausdorff error is bounded by an envelope tending to zero.

## Verified conclusion

`d_H(K_n, frontier(inside)) -> 0`.

## Honest scope

The abstract theorem is conditional. It identifies the exact reusable bridge but does not construct a computable boundary family for an arbitrary domain.

## NEXT_POINT

IF-BS-22F-E: formulate a boundary-preserving transport theorem. Show that an isometry or controlled bi-Lipschitz map transports the three side labels and the Hausdorff-convergent interface family to a noncircular chamber.
