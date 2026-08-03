# Passport IF-BS-08

Date: 2026-07-31
Object: exact 4x refinement of the IF-BS-07 radial digital contour.
Status: Lean-verified research slice.

## Inputs

- Coarse grid: 5x5, spacing 1.
- Fine grid: 17x17, spacing 1/4 on the same normalized square.
- Fine field numerator: `F4(i,j)=(i-8)^2+(j-8)^2`.
- Exact threshold correspondence: `F4<=32` iff `F<=2` at embedded nodes.
- Embedding: `E(k)=4k`.
- Coarsening: `C(i)=floor(i/4)`, with `C(16)=4`.
- Fine crossing: endpoint inside flags differ.
- Localization radius: four quarter-steps, exactly one coarse cell.

## Checked outputs

1. The refined grid has 289 nodes.
2. The refined graph has 544 unit edges.
3. The refined threshold region has 101 nodes.
4. Exhaustive filtering produces exactly 44 contour edges.
5. Every reported fine edge is adjacent and crosses the exact threshold.
6. Every crossing fine-grid edge is reported.
7. The fine scalar equals 16 times the coarse scalar on embedded points.
8. Fine and coarse inside predicates agree on embedded points.
9. Coarsening after embedding is the identity.
10. Every fine axis coordinate is within three quarter-steps of its anchor.
11. Both endpoints of every fine contour edge lie within one coarse cell of a
    coarse contour endpoint.
12. A separate audit reconstructs these claims through the exported API.

## Verification

- Toolchain: Lean 4.32.1.
- Main and independent audit modules compile successfully.
- Source gap scan: no `axiom`, `sorry`, or `admit` declarations.
- Counts, embedding compatibility, left inverse, coordinate error, and the
  exhaustive all-edges localization theorem use no axioms.
- The membership-to-certificate theorem uses only `propext` and `Quot.sound`;
  the exact contour-membership iff uses only `propext`.

## Claim boundary

This proves a finite coarse-to-fine localization invariant. It is not a uniform
theorem over arbitrary mesh sizes, a smooth level-set convergence theorem, or a
physical calibration of PlanckTouch.

## Next slice

Define an indexed family of odd radial grids with spacing `1/(2n)` and an
abstract refinement map. Replace finite exhaustion by a uniform arithmetic
bound and state a Hausdorff-style localization theorem independent of a fixed
grid size.
