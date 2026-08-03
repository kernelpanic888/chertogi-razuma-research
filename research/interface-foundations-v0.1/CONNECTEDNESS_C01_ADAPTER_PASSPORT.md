# Passport: IF-BS-C01 connectedness adapter

## Question

Does the published C-01 connectedness reader remove the connectedness premise
from the boundary-of-self lemma?

## Answer

No, not automatically. It supplies the transition architecture. IF-BS-18
supplies concrete graph connectedness for the radial inside and outside
carriers. A separate transport theorem is still needed to obtain topological
connectedness of the ambient closure space used by IF-BS-01.

## Formal objects

- `C01Carrier`
- `C01Reachable`
- `C01Connected`
- `insideCarrier_connected`
- `outsideCarrier_connected`
- `C01TopologicalRealization`
- `topologicalSelf_hasBoundary_via_c01`

## Dependency chain

`C-01 transition pattern -> IF-BS-18 finite reachability -> C01Connected`

`C01Connected -> explicit connectedness transport -> IsConnected -> IF-BS-01`

## Claim status

- Concrete radial graph connectedness: proved.
- Generic C-01-to-topology implication: exposed as an obligation.
- Arbitrary-world connectedness: not claimed.

## Verification

- Main module: Lean 4.32.1 pass.
- Independent audit: Lean 4.32.1 pass.
- Source scan: no `axiom`, `sorry`, or `admit`.
- Adapter theorem: axiom-free.
- Radial connectivity and boundary corollary: only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Red boundary

The C-01 public reader's unary `connected : State -> Prop` is an uninterpreted
predicate in its bridge sketch. It is not the same object as binary path
reachability or global topological connectedness.

## Next point

Construct the finite-grid closure topology induced by unit adjacency and prove
that `C01Connected` transports to `IsConnected` for the radial carriers. Then
decide whether this local result can support, rather than replace, the general
connectedness premise on the public page.
