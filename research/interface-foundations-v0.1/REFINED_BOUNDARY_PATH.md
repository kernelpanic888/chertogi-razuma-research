# IF-BS-04 / Refined Boundary Path

Status: finite refinement test for a threshold interface.

## 1. Same interval, two resolutions

The coarse path samples the distinguishability levels

\[
G_2=(0,2,4),
\]

while the refined path samples

\[
G_4=(0,1,2,3,4).
\]

Both use the same threshold \(\varepsilon=2\) and the same strict admission
rule

\[
I_\varepsilon(x)=1
\quad\Longleftrightarrow\quad
\varepsilon<D(x).
\]

The state sequences are therefore

\[
G_2:\quad 0\;0\;1,
\qquad
G_4:\quad 0\;0\;0\;1\;1.
\]

## 2. Interface computed from edges

For neighbouring nodes \(x\sim y\), let

\[
Cross_\varepsilon(x,y)
:=
I_\varepsilon(x)\oplus I_\varepsilon(y).
\]

A node belongs to the finite PlanckTouch band when it meets a crossing edge.
The computation gives

\[
PT_2(G_2)=\{c_1,c_2\},
\qquad
PT_2(G_4)=\{f_2,f_3\}.
\]

Each path has exactly one crossing edge. No boundary node is selected by name;
the band is obtained from the change of state.

## 3. Refinement map

Define the resolution-loss map

\[
\rho(f_0)=c_0,
\quad
\rho(f_1)=c_0,
\quad
\rho(f_2)=c_1,
\quad
\rho(f_3)=c_2,
\quad
\rho(f_4)=c_2.
\]

Lean proves both directions:

\[
x\in PT_2(G_4)
\Longrightarrow
\rho(x)\in PT_2(G_2),
\]

and every coarse boundary node has a fine boundary lift. Equivalently,

\[
PT_2(G_2)
=
\rho\bigl(PT_2(G_4)\bigr).
\]

This is exact refinement stability for the first nontrivial multi-level path.

## 4. Meaning

The interface moves from the coarse edge \((2,4)\) to the tighter edge
\((2,3)\), but it does not disappear or jump to an unrelated region. After
forgetting the added resolution, the refined band returns exactly to the coarse
band.

The result supplies a testable form of the idea that PlanckTouch is a
resolution-dependent band around a persistent threshold crossing, rather than
an absolute positive gap.

## 5. Red boundary

This theorem concerns two declared finite samplings and one declared coarsening
map. It is not yet convergence for an infinite sequence of meshes. The graph
band is a combinatorial frontier; identifying its limit with a physical boundary
requires a metric realization, a mesh-size parameter, and a convergence bound.
