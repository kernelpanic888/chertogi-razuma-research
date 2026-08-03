# IF-BS-05 / General Boundary Mesh

Status: general finite-mesh localization theorem and reciprocal-scale limit.

## 1. Mesh family

For every \(n\ge1\), let

\[
G_n=\left\{0,\frac1n,\frac2n,\ldots,1\right\}.
\]

Choose an integer threshold index \(k<n\). A node is admitted when its index is
strictly above the threshold:

\[
I_k(i)=1
\quad\Longleftrightarrow\quad
k<i.
\]

An edge \((i,i+1)\) crosses the interface exactly when its endpoint states
differ.

## 2. Unique crossing theorem

Lean proves for arbitrary natural \(i\) and \(k\):

\[
Cross_k(i,i+1)
\quad\Longleftrightarrow\quad
i=k.
\]

Therefore the finite PlanckTouch band on every mesh is exactly

\[
PT_k(G_n)=\{k,k+1\}.
\]

There is one crossing edge, its endpoints are distinct, and its index width is

\[
(k+1)-k=1.
\]

Unlike IF-BS-04, this is not a calculation for two chosen paths. It holds for
every \(n\) and every internal threshold \(k<n\).

## 3. Normalized width

After realizing the mesh on the unit interval, one index cell has width

\[
\Delta_n=\frac1n.
\]

Lean records this as a positive unit fraction and proves antitonicity under
refinement:

\[
m\le n
\Longrightarrow
\Delta_n\le\Delta_m.
\]

It also proves the reciprocal-basis form of convergence:

\[
\forall m\ge1\;\exists N=m\;\forall n\ge N:
\Delta_n\le\frac1m.
\]

Hence the physical width of the computed band can be made smaller than every
reciprocal resolution scale while the crossing edge continues to exist.

## 4. Result

The finite model now separates two statements:

\[
\text{combinatorial persistence:}
\qquad
|PT_k(G_n)|_{\mathrm{edges}}=1,
\]

\[
\text{metric contraction:}
\qquad
\Delta_n=\frac1n\longrightarrow0.
\]

This is the precise version of a persistent interface whose observable band
shrinks with increasing resolution. It supports reading PlanckTouch as a
resolution band, not as a universal positive distance built into continuous
geometry.

## 5. Red boundary

Lean checks convergence on the reciprocal basis \(1/m\). A full theorem in the
usual real-valued epsilon language still requires an ordered-field library and
an explicit embedding of the finite meshes into a metric space.

The model proves persistence and contraction for a monotone one-dimensional
threshold. It does not yet prove the same result for curved boundaries,
branching graphs, noisy measurements, or physical spacetime.
