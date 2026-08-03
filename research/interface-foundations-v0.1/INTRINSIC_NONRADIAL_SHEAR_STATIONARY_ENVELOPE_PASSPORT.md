# Passport IF-BS-22F-F8C22

Status: Lean-verified local envelope theorem

Date: 2026-08-01

## Question

Can the compact scalar maximum left abstract in F8C21 be replaced by a unique, checkable algebraic point, especially at amplitude \(a=1/2\)?

## Carrier

`formal/IntrinsicNonradialShearStationaryEnvelope.lean`

Audit: `formal/IntrinsicNonradialShearStationaryEnvelopeAudit.lean`

## Verified exports

- The dominant branch \(X\ge Y\) parameterizes every relevant maximum by \(t=Y/X\in[0,1]\).
- The stationary balance \(K_a\) is strictly increasing for every \(a\ge0\).
- It has exactly one root in \([0,1]\).
- The exact profile increases before that root and decreases after it.
- The F8C21 compact envelope equals the profile value at the unique root.
- At \(a=1/2\), the root satisfies the quartic certificate and lies strictly in \((21/25,17/20)\).
- The exact local tangent modulus at \(a=1/2\) equals the certified profile value.

## Red boundary

No global path-to-chord theorem is claimed. Exact infinitesimal optimization is not yet a proof of the least global pairwise Lipschitz constant for the ambient max product metric.

## Next

IF-BS-22F-F8C23: prove a chamber-internal path-length bound sharp enough to compare tangent length with ambient chord distance, or produce a direct pairwise counterexample showing that the local modulus cannot be globalized unchanged.
