# IF-BS-01 / Boundary of Self

Status: standard topological implication plus an authorial interpretation of
identity and selfhood.

## 1. Topological core

Let X be a connected topological space and let A be a subset of X. Its boundary
is

\[
\partial A
:=
\overline A\cap\overline{X\setminus A}.
\]

If the boundary is empty, A is both open and closed. Connectedness therefore
implies

\[
\partial A=\varnothing
\Longrightarrow
A=\varnothing
\ \lor\
A=X.
\]

Equivalently,

\[
X\text{ connected},
\qquad
\varnothing\ne A\ne X
\Longrightarrow
\partial A\ne\varnothing.
\]

Human reading: in a connected world, anything that is neither nothing nor
everything must have a boundary.

## 2. Minimum self-description

Membership in A supplies the characteristic map

\[
\chi_A:X\to\{0,1\},
\qquad
\chi_A(x)=
\begin{cases}
1,&x\in A,\\
0,&x\notin A.
\end{cases}
\]

This is a logical binary distinction, not a claim that every physical identity
stores exactly one Shannon bit.

Choose an internal point p. The model record of a self is

\[
\operatorname{Self}(p,A)
:=
p\in\operatorname{Int}(A)
\land
X\setminus A\ne\varnothing
\land
\partial A\ne\varnothing.
\]

The point alone does not define a self. It becomes an internal point only
relative to a region, a complement, and their interface.

### Concrete closure model

The Lean layer now represents topology by a Kuratowski closure operator
\(c:\mathcal P(X)\to\mathcal P(X)\): it is extensive, monotone, idempotent,
preserves the empty region, and preserves finite unions. The derived objects are

\[
\operatorname{Int}_c(A)=X\setminus c(X\setminus A),
\qquad
\partial_c A=c(A)\cap c(X\setminus A).
\]

Connectedness is stated in its clopen form: every simultaneously open and
closed region is empty or whole. From these definitions Lean derives, rather
than assumes,

\[
\partial_c A=\varnothing
\Longrightarrow
A=\varnothing\ \lor\ A=X.
\]

### Resolved identity region

For a natural-valued distinguishability record \(D\), reference \(a\), and
resolution threshold \(\varepsilon\), define

\[
X_\varepsilon(a)
:=
\{b\in X\mid \varepsilon<D(a,b)\}.
\]

If

\[
D(a,a)=0,
\qquad
\exists b\in X:\ \varepsilon<D(a,b),
\]

then \(X_\varepsilon(a)\) is nonempty, while \(a\notin X_\varepsilon(a)\).
It is therefore a proper region. In a connected closure topology Lean proves

\[
\partial_c X_\varepsilon(a)\ne\varnothing.
\]

This is the first checked bridge from a resolution threshold to an unavoidable
interface. It does not yet identify \(D\) with a physical metric or
\(\varepsilon\) with the Planck scale.

## 3. Interface reading

\[
\text{something}
=
\text{interior}
+
\text{exterior}
+
\text{interface}.
\]

If a proper region loses its boundary while the ambient space remains connected,
it cannot remain that proper region. It collapses toward one of the two
degenerate readings: empty or whole.

This creates the bridge

\[
\text{first distinction}
\longrightarrow
\text{boundary of identity}
\longrightarrow
\text{resolved interface}
\longrightarrow
\text{field and path memory}.
\]

## 4. Red boundary

Connectedness is essential. A disconnected space can contain a nonempty proper
component that is both open and closed and therefore has empty boundary.

The topological theorem concerns subsets and boundaries. Interpreting p as a
conscious first-person point is an author model, not a theorem of neuroscience
or a demonstrated physical law.

The nontriviality theorem also needs a distinguishable witness above the
threshold. A zero self-distance alone does not prove that such a witness exists.
