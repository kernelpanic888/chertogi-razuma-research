# Passport IF-BS-04

Date: 2026-07-31
Object: exact stability of a computed threshold band under one refinement.

## Inputs

- Coarse levels: 0, 2, 4.
- Fine levels: 0, 1, 2, 3, 4.
- Shared threshold: eps = 2.
- Admission: eps < D.
- Path adjacency: consecutive nodes only.
- Coarsening: (f0,f1,f2,f3,f4) -> (c0,c0,c1,c2,c2).

## Checked outputs

1. The coarse state profile is 0,0,1.
2. The fine state profile is 0,0,0,1,1.
3. Each path has exactly one crossing edge.
4. The coarse band is {c1,c2}.
5. The fine band is {f2,f3}.
6. Every fine band node maps to a coarse band node.
7. Every coarse band node has a fine band lift.
8. Lean proves CoarseBand = image(coarsen, FineBand) extensionally.

## Claim boundary

This is exact stability for one finite refinement pair. It is not a general
convergence theorem and does not assign a physical length to eps.

## Next slice

Generalize from the fixed paths to a family of meshes indexed by n. Introduce a
normalized coordinate and prove that every band lies within one mesh cell of the
threshold, so its physical width tends to zero while the crossing persists.
