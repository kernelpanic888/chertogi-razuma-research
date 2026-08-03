# IF-BS-06 / Rational Boundary Limit

Status: standard epsilon-N convergence over positive rational scales.

## 1. Rational embedding

Every node \(i\) of \(G_n\) is embedded into the unit interval as

\[
\iota_n(i)=\frac{i}{n},
\qquad
0\le i\le n.
\]

For a threshold index \(k<n\), the two PlanckTouch endpoints become

\[
\iota_n(k)=\frac{k}{n},
\qquad
\iota_n(k+1)=\frac{k+1}{n}.
\]

Lean verifies that their numerator gap is exactly one, so their rational cell
width is

\[
\Delta_n=\frac1n.
\]

## 2. Exact rational order

A positive rational scale is represented by positive integers \(p,q\):

\[
\varepsilon=\frac pq,
\qquad
p>0,
\quad
q>0.
\]

The strict order is checked by cross multiplication. Thus

\[
\frac1n<\frac pq
\quad\Longleftrightarrow\quad
q<pn.
\]

This representation does not require decimal approximation and does not assume
that the fraction is already reduced.

## 3. Epsilon-N theorem

For every positive rational \(\varepsilon=p/q\), choose

\[
N=q+1.
\]

For every \(n\ge N\), positivity of \(p\) gives

\[
q<n\le pn,
\]

and therefore

\[
\frac1n<\frac pq=\varepsilon.
\]

Lean proves the full statement

\[
\forall\varepsilon\in\mathbb Q_{>0}\;
\exists N\;
\forall n\ge N:\
\Delta_n<\varepsilon.
\]

Together with IF-BS-05 this yields

\[
\text{the crossing persists for every mesh,}
\qquad
\text{the width of its band tends to zero.}
\]

## 4. Reading

The model no longer merely says that finer meshes are better. It supplies a
witness \(N\) for every declared rational tolerance. The interface remains
combinatorially present while no fixed positive rational width survives all
refinements.

This makes the current PlanckTouch reading sharper:

\[
PlanckTouch
=
\text{persistent crossing}
+
\text{resolution-dependent band},
\]

not an absolute minimal positive distance in continuous geometry.

## 5. Red boundary

The theorem is standard epsilon-N convergence for positive rational tolerances.
Extending it to real tolerances is routine mathematically but remains outside
the current dependency-free Lean layer.

No physical length scale has been derived. Connecting \(1/n\) to the Planck
length requires a declared calibration map and empirical semantics.
