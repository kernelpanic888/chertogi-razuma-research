# IF-GF-01 / Distinction-Holonomy Field

Status: conditional author model. The logical implications are machine checked;
the identification with fundamental physics is open.

## 1. State space and local pole

Let S be a state space with operational distinguishability

\[
D:S\times S\to\mathbb R_{\ge 0}.
\]

For a resolution threshold epsilon > 0 define

\[
X_\varepsilon
:=
\{(a,b)\in S\times S\mid D(a,b)>\varepsilon\}.
\]

The local pole is the first positive boundary band

\[
P_-(a,b)
\Longleftrightarrow
0<D(a,b)\le\varepsilon.
\]

Absolute merger is D(a,b)=0. The model does not call that an interface state:
there are no distinguishable sides left to carry an interface.

## 2. Field bridge

Let A be a U(1) connection and

\[
F=dA
\]

its local curvature. A closed path gamma carries the holonomy

\[
W_q(\gamma)
:=
\exp\left(
\frac{iq}{\hbar}\oint_\gamma A
\right).
\]

When gamma bounds a surface Sigma and A is defined on that surface,

\[
W_q(\partial\Sigma)
=
\exp\left(
\frac{iq}{\hbar}\int_\Sigma F
\right).
\]

This is the typed bridge. The local quantity F does not map directly to a
homotopy class. It is integrated over a surface; the boundary path records the
result as a gauge-invariant phase.

Define field distinguishability by

\[
D_F(\gamma):=|1-W_q(\gamma)|.
\]

Then the local pole can be read as

\[
0<D_F(\gamma)\le\varepsilon_F.
\]

## 3. Global return pole

For a closed admissible path, define the finite return order when it exists:

\[
\operatorname{ord}(W_q(\gamma))
:=
\min\{n\ge1\mid W_q(\gamma)^n=1\}.
\]

The global pole is

\[
P_+(\gamma,n)
\Longleftrightarrow
W_q(\gamma)^n=1
\ \land\
\forall\,0<k<n,\ W_q(\gamma)^k\ne1.
\]

The rotation example is a separate established topology:

\[
\pi_1(SO(3))\cong\mathbb Z_2,
\qquad
[\gamma_{2\pi}]\ne e,
\qquad
[\gamma_{4\pi}]=e.
\]

Thus 360 degrees restores visible orientation but not the path class; 720
degrees closes the remembered path. No special topological statement is attached
to 380 degrees.

## 4. Shared admissibility law

Let Inv be any invariant preserved by admissible evolution. Then

\[
\operatorname{Admissible}(\gamma)
\Longrightarrow
\operatorname{Inv}(\gamma(0))
=
\operatorname{Inv}(\gamma(1)).
\]

Therefore

\[
\operatorname{Inv}(\gamma(0))
\ne
\operatorname{Inv}(\gamma(1))
\Longrightarrow
\gamma\cap\partial X_{\rm adm}\ne\varnothing.
\]

For links this means that changing a linking invariant requires a crossing, cut,
singularity, or departure from the selected configuration space.

## 5. The model-external monopole

Let P_IF be this physics and let M(F) mean a nonzero closed magnetic flux:

\[
M(F)
\Longleftrightarrow
\exists\,S^2:
\int_{S^2}F\ne0.
\]

The defining closure axiom of P_IF is global exactness:

\[
\mathcal P_{\rm IF}(F)
\Longrightarrow
\exists A\ \text{global}:F=dA.
\]

For every closed two-surface, Stokes then gives

\[
\int_{S^2}F
=
\int_{S^2}dA
=
\int_{\partial S^2}A
=0.
\]

Hence the conditional no-monopole lemma is

\[
\mathcal P_{\rm IF}(F)
\Longrightarrow
\neg M(F).
\]

Equivalently,

\[
M(F)
\Longrightarrow
\neg\mathcal P_{\rm IF}(F).
\]

If a theory T contains P_IF and proves not-M, adjoining M makes that theory
inconsistent:

\[
T\vdash\neg M
\Longrightarrow
T+M\vdash\bot.
\]

This is the precise sense in which a monopole destroys the present
axiomatization. It does not prove that monopole mathematics is inconsistent.
Standard monopole models instead abandon global single-chart exactness and use
nontrivial U(1) bundles with local potentials joined on overlaps.

## 6. Electromagnetic dual sector

With electric and magnetic source forms,

\[
dF=J_m,
\qquad
d\star F=J_e.
\]

Inside P_IF the magnetic source sector is fixed to J_m=0. A nonzero J_m is an
external-domain witness: it announces that the global closure axiom has failed.

## 7. Red boundary

Established mathematics supplies curvature, holonomy, Stokes, rotation topology,
ambient isotopy, and nontrivial bundle descriptions of monopoles. P_IF adds the
authorial physical axiom of global exactness. No experiment has established that
this axiom is universal, so the no-monopole conclusion is conditional on the
model and must not be presented as an empirical fact.

## Sources

- Y. Aharonov and D. Bohm, Significance of Electromagnetic Potentials in the Quantum Theory:
  https://journals.aps.org/pr/abstract/10.1103/PhysRev.115.485
- D. Gaiotto, A. Kapustin, N. Seiberg, B. Willett, Generalized Global Symmetries:
  https://arxiv.org/abs/1412.5148
- P. A. M. Dirac, The Theory of Magnetic Poles:
  https://journals.aps.org/pr/abstract/10.1103/PhysRev.74.817
- T. T. Wu and C. N. Yang, Dirac's Monopole Without Strings:
  https://journals.aps.org/prd/abstract/10.1103/PhysRevD.14.437

