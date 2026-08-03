# F8C22: Unique stationary envelope

## Result

The compact optimizer from F8C21 is reduced to one normalized slope coordinate

\[
t=Y/X\in[0,1],\qquad
(X,Y)=\frac{(1,t)}{\sqrt{1+t^2}}.
\]

The dominant branch is sufficient: if \(X<Y\), swapping the coordinates cannot decrease the scalar tangent density. On the branch \(X\ge Y\), the exact profile is

\[
F_a(t)=\frac{1+t}{1+t^2}+
\frac{a+(1+a)t}{\sqrt{1+t^2}}.
\]

Its derivative has the exact sign factorization

\[
F_a'(t)=-\frac{K_a(t)}{(1+t^2)^{3/2}},
\qquad
K_a(t)=\frac{t^2+2t-1}{\sqrt{1+t^2}}+at-(1+a).
\]

For every \(a\ge0\),

\[
K_a'(t)=\frac{t^3+3t+2}{(1+t^2)^{3/2}}+a>0
\quad (0\le t\le1),
\]

while \(K_a(0)=-(2+a)<0\) and \(K_a(1)=\sqrt2-1>0\). Therefore there is exactly one root \(t_a\in(0,1)\), the profile increases before it and decreases after it, and \(t_a\) is the unique maximizer.

The original compact envelope is no longer an opaque chosen maximum:

\[
E(a)=F_a(t_a),\qquad L_{\mathrm{tan}}(a)=2aF_a(t_a).
\]

## Half-amplitude certificate

At \(a=1/2\), the unique root satisfies

\[
3t^4+22t^3-2t^2-10t-5=0,
\qquad \frac{21}{25}<t<\frac{17}{20}.
\]

The rational bracket selects the physical root and excludes the extraneous branches introduced by squaring. The certified numerical reading is

\[
t_{1/2}\approx0.8468203639,
\qquad
L_{\mathrm{tan}}(1/2)=F_{1/2}(t_{1/2})\approx2.4264688493.
\]

The decimal is a visualization of the exact root certificate, not a premise of the proof.

## Honest boundary

F8C22 closes the exact local tangent optimization and the half-amplitude algebraic certificate. It still does not identify this infinitesimal modulus with the least global pairwise Lipschitz constant in the ambient chord metric. The remaining theorem is a path-to-chord bridge or an independent direct pairwise optimization.
