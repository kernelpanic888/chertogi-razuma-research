# IF-BS-08 / Refined Curved Boundary Grid

Status: Lean-verified finite refinement and localization certificate.

## 1. Same field, finer coordinates

The coarse grid uses coordinates (0,1,2,3,4). The refined grid uses

\[
G_{17,17}=\{0,1,\ldots,16\}^2
\]

with normalized physical coordinate (u=n/4). Its centre is (n=8), so the
integer field stores the exact numerator

\[
F_4(i,j)=(i-8)^2+(j-8)^2=16F(i/4,j/4).
\]

The old threshold (F\le2) therefore becomes exactly

\[
F_4\le32.
\]

No floating-point approximation is used.

## 2. Exact coarse/fine compatibility

The coarse embedding is

\[
E(k)=4k.
\]

Lean proves for every coarse point (p):

\[
F_4(Ep)=16F(p),
\qquad
Inside_4(Ep)=Inside(p).
\]

The coarsening map is (C(i)=\lfloor i/4\rfloor), with the terminal point
(16\mapsto4). It is a left inverse of the embedding:

\[
C(Ep)=p.
\]

Every fine coordinate lies at most three quarter-steps from its coarse anchor:

\[
|i-4C(i)|\le3<4.
\]

## 3. Computed contour

The refined graph contains 289 nodes and 544 horizontal or vertical unit
edges. The exact threshold contains 101 nodes. Filtering all 544 edges by the
endpoint XOR predicate produces a 44-edge contour.

For each reported fine edge (e=(p,q)), Lean certifies

\[
Adjacent_4(e)\land Cross_4(e).
\]

The converse is also proved relative to the generated graph, so no crossing
edge is omitted.

## 4. Localization theorem

Distance is measured in quarter-cell units. A fine point is near the coarse
contour when some endpoint (c) of a coarse contour edge satisfies

\[
d_\infty(p,4c)\le4.
\]

Lean exhausts the computed fine contour and proves

\[
e=(p,q)\in Contour_4
\Longrightarrow
Near(p,Contour_1)\land Near(q,Contour_1).
\]

Thus both endpoints of every fine crossing edge remain within one normalized
coarse cell of the certified coarse contour.

## 5. Red boundary

This is one exact finite refinement, not a convergence theorem for all mesh
sizes. The proof does not establish Hausdorff convergence to a smooth circle,
an asymptotic rate, or physical Planck-length calibration. The localization
predicate compares contour endpoints; it does not yet construct a continuous
interpolated curve.

## 6. Verification record

- Lean: 4.32.1.
- Main module: `formal/RefinedCurvedBoundaryGrid.lean`.
- Independent import audit: `formal/RefinedCurvedBoundaryGridAudit.lean`.
- No project `axiom`, `sorry`, or `admit` is declared.
- Counts, scalar compatibility, inside compatibility, `C(Ep)=p`, the axis error
  bound, and exhaustive localization are computationally closed with no axioms.
- Extracting the per-edge localization certificate from list membership uses
  only Lean's `propext` and `Quot.sound`; the exact reported-edge iff uses only
  `propext`.
