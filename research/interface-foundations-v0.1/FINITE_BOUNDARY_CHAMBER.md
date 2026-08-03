# IF-BS-03 / Finite Boundary Chamber

Status: executable two-point witness for the boundary theorem.

## 1. Chamber

Take

\[
X_2=\{0,1\},
\qquad
D(x,y)=
\begin{cases}
0,&x=y,\\
2,&x\ne y,
\end{cases}
\qquad
\varepsilon=1.
\]

With reference point \(a=0\), the resolved identity region is computed rather
than assumed:

\[
X_\varepsilon(0)
=\{b\in X_2\mid 1<D(0,b)\}
=\{1\}.
\]

Thus \(0\notin X_\varepsilon(0)\), \(1\in X_\varepsilon(0)\), and the region is
nonempty and proper.

## 2. Connected closure

The chamber uses the indiscrete Kuratowski closure

\[
c(A)=
\begin{cases}
\varnothing,&A=\varnothing,\\
X_2,&A\ne\varnothing.
\end{cases}
\]

Lean verifies all five closure laws and proves this topology connected. Since
both \(X_\varepsilon(0)\) and its complement are nonempty,

\[
c(X_\varepsilon(0))=X_2,
\qquad
c(X_2\setminus X_\varepsilon(0))=X_2,
\]

and therefore

\[
\partial_c X_\varepsilon(0)=X_2.
\]

## 3. Computed transition band

Let the two points be adjacent exactly when they differ. Define the finite
transition band

\[
PT_\varepsilon(A)
:=
\{x\in X_2\mid
\exists y:\ x\ne y
\land
(x\in A\leftrightarrow y\notin A)\}.
\]

For the computed region \(X_\varepsilon(0)=\{1\}\), both points touch the sole
cross-threshold edge. Lean proves the extensional equality

\[
\partial_c X_\varepsilon(0)
=
PT_\varepsilon(X_\varepsilon(0))
=
X_2.
\]

This is the first chamber in which the topological frontier and a separately
computed transition band coincide.

## 4. Reading

The reference point does not belong to the resolved region because it is
indistinguishable from itself. The other point enters the region because its
distance crosses the chosen resolution threshold. The interface is not added by
hand: it appears from the topology and agrees with the edge computation.

## 5. Red boundary

The chamber is deliberately minimal and uses an indiscrete topology. It proves
that the bridge is executable and internally consistent; it does not establish
that physical spacetime is indiscrete, that distinguishability is
natural-valued, or that \(\varepsilon\) is the Planck scale.

The equality with \(PlanckTouch_\varepsilon\) is presently a finite-model
candidate. A physical claim requires a richer finite approximation, a declared
adjacency rule, convergence under refinement, and observational semantics.
