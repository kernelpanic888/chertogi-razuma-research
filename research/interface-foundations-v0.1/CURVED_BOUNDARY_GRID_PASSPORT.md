# Passport IF-BS-07

Date: 2026-07-31
Object: a certified digital contour on a radial 2D scalar field.
Status: Lean-verified research slice.

## Inputs

- Grid: 5x5 nodes.
- Axis coordinates: 0,1,2,3,4.
- Radial squared offsets: 4,1,0,1,4.
- Scalar field: F(x,y)=dx^2+dy^2.
- Inside threshold: F<=2.
- Adjacency: horizontal or vertical unit edge.
- Crossing: endpoint inside flags differ.

## Checked outputs

1. The generated grid has 25 nodes.
2. The generated grid has 40 unit edges.
3. The threshold region has 9 nodes.
4. Filtering all edges produces a 12-edge contour.
5. Every contour edge crosses the threshold.
6. Every contour edge joins adjacent grid nodes.
7. Every crossing grid edge is included in the contour.
8. Lean proves Contour(e) iff GridEdge(e) and Cross(e).
9. A separate audit imports the public theorem surface and reconstructs the
   four counts, the combined adjacency/crossing certificate, and the iff.

## Verification

- Toolchain: Lean 4.32.1.
- Main module: `formal/CurvedBoundaryGrid.lean`.
- Audit module: `formal/CurvedBoundaryGridAudit.lean`.
- Source gap scan: no `axiom`, `sorry`, or `admit` declarations.
- Computational count theorems: no axioms.
- Membership theorems: only `propext` and, where list membership equality is
  unfolded, `Quot.sound`.

## Claim boundary

This is a certified finite digital contour. It is not yet a theorem of smooth
level-set convergence and carries no physical Planck-length calibration.

## Next slice

Construct the same radial field on a finer grid and define a coarsening map.
Measure contour localization in normalized coordinates and prove that every fine
crossing edge remains within one coarse cell of the coarse contour.
