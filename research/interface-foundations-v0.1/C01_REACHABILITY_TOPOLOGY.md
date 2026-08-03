# IF-BS-C02: reachability topology

## Construction

For a C-01 carrier `C`, the points of the space are the admissible states of
`C`. For a region `A`, define its closure by

`cl_C(A) = { y | there exists x in A such that x reaches y }`.

Finite reachability is reflexive and transitive, so this operator is extensive,
monotone, idempotent, preserves the empty region, and preserves binary unions.
It therefore defines a Kuratowski closure topology.

## Theorem

If every pair of admissible states is joined by a directed admissible path,
then the reachability topology is connected:

`C01Connected(C) -> IsConnected(T_C)`.

Consequently, every proper region of `T_C` has nonempty topological boundary,
and every topological self-record in `T_C` has a boundary.

## Radial realization

IF-BS-18 proves `C01Connected` for the sampled radial inside carrier and, when
`m > 0`, for the sampled radial outside carrier. IF-BS-C02 therefore proves
that both induced reachability topologies are connected.

## Red boundary

This is a topology on one admissible carrier, hence on one graph component. It
does not prove that an arbitrary ambient world is connected, and it does not
identify graph closure with Euclidean closure. The general IF-BS-01 premise
must remain visible until such an ambient realization is constructed.
