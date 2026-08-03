# IF-BS-07 / Curved Boundary Grid

Status: Lean-verified two-dimensional digital contour (IF-BS-07).

## 1. Grid and field

Take the \(5\times5\) lattice

\[
G_{5,5}=\{0,1,2,3,4\}^2
\]

with centre \((2,2)\). Define the radial discrete field

\[
F(x,y)=(x-2)^2+(y-2)^2,
\]

where the squared offsets on each axis are stored exactly as

\[
4,1,0,1,4.
\]

A node is inside when

\[
F(x,y)\le2.
\]

The computation produces nine inside nodes: the digital radial core around the
centre.

## 2. Contour computation

The grid contains 25 nodes and 40 horizontal or vertical edges. For every edge
\(e=(p,q)\), define

\[
Cross(e)=Inside(p)\oplus Inside(q).
\]

The contour is not supplied as a preferred list. Lean constructs all 40 edges
and filters them by \(Cross(e)\). The resulting contour contains exactly 12
edges.

## 3. Certification

Lean proves:

\[
e\in Contour
\Longrightarrow
Adjacent(e)\land Cross(e),
\]

and the converse relative to the generated grid:

\[
e\in GridEdges\land Cross(e)
\Longrightarrow
e\in Contour.
\]

Equivalently,

\[
e\in Contour
\quad\Longleftrightarrow\quad
e\in GridEdges\land Cross(e).
\]

Thus every published contour edge genuinely joins neighbouring nodes on
opposite sides of the declared level, and no crossing grid edge is omitted.

The certificate is exported as one conjunction:

\[
e\in Contour
\Longrightarrow
Adjacent(e)=true\;\land\;Cross(e)=true.
\]

## 4. Geometry

The one-dimensional result \(\{k,k+1\}\) has become a closed digital contour
around a radial level set. PlanckTouch is now represented by a family of local
crossing cells rather than a single distinguished point.

This supplies the two-dimensional candidate:

\[
PlanckTouch_\varepsilon(F)
=
\{e\in GridEdges\mid
I_\varepsilon(e_0)\oplus I_\varepsilon(e_1)=1\}.
\]

## 5. Red boundary

The field is radial, but its \(5\times5\) contour is digital and polygonal. The
theorem certifies the discrete level-set extraction; it does not prove
convergence to a smooth circle.

Metric convergence requires a sequence of finer two-dimensional grids, a
coarsening or interpolation rule, and a bound between the digital contour and
the target continuous level set.

## 6. Verification record

- Lean: 4.32.1.
- Source: `formal/CurvedBoundaryGrid.lean`.
- Independent import audit: `formal/CurvedBoundaryGridAudit.lean`.
- Counts and Boolean exhaustions are closed by computation and use no axioms.
- The exported membership certificates use only Lean's `propext` and
  `Quot.sound`; no project axiom, `sorry`, or `admit` is declared.
- The full dependency chain from `BoundaryOfSelf` through
  `RationalBoundaryLimit` was rebuilt before this certificate was recorded.
