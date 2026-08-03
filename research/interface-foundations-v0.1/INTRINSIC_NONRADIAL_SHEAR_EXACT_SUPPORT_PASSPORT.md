# Passport IF-BS-22F-F8C5

## Name

Intrinsic nonradial shear: exact support closure and metric refinement.

## Status

Lean verified with an independent audit. Main and audit compile; the source
scan contains no `axiom`, `sorry`, or `admit`. Audited dependencies are the
standard `[propext, Classical.choice, Quot.sound]`.

## Input

- IF-BS-22F-F8C4 intrinsic shear (S_a(x,y)=(x,y+aarphi(x)arphi(y))).
- Tent bump (arphi(t)=max(0,1-|t|)).
- Ambient Euclidean plane and the existing homeomorphism for
  (0le ale 1/4).

## Obligations

1. Characterize the actual moving set for every (a>0).
2. Identify its exact closure.
3. Prove compactness and the four-edge frontier.
4. Prove minimality among closed identity-outside carriers.
5. Replace the old kernel coefficient (2) by (sqrt2).
6. Derive direct, co-Lipschitz, and inverse metric bounds.
7. Exhibit exact axial lower bounds.
8. Keep the full two-dimensional spectral optimum outside the verified claim.

## Formal artifacts

- `formal/IntrinsicNonradialShearExactSupport.lean`
- `formal/IntrinsicNonradialShearExactSupportAudit.lean`

## Main result

[
overline{{p:S_a(p)
e p}}=[-1,1]^2,
qquad
partial[-1,1]^2=
([-1,1]	imes{-1,1})cup({-1,1}	imes[-1,1]).
]

[
(1-sqrt2a)dle dcirc(S_a	imes S_a)le(1+sqrt2a)d,
qquad
operatorname{Lip}(S_a^{-1})lerac1{1-sqrt2a}.
]

## Red boundary

- The old circular carrier was safe but not minimal.
- The coefficient (sqrt2) is a proved global envelope for the kernel.
- The optimal singular-value constants of the complete planar map remain open.
- The construction is mathematical and computational, not a claim of a
  measured physical minimum.

## Next passport step

IF-BS-22F-F8C6: construct diagonal near-origin probes, prove sharpness of the
kernel coefficient (sqrt2), and derive or refute the candidate optimal
spectral constants for the complete planar shear.
