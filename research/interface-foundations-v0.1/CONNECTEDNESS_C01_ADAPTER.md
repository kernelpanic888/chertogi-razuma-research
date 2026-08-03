# IF-BS-C01: connectedness adapter

## Result

The C-01 reader and IF-BS-01 use related but non-identical notions of
connectedness.

- C-01 supplies an admissible field of states, transitions, selection, and
  invariant transport.
- IF-BS-18 proves literal finite-path connectedness for the sampled radial
  chamber: all inside samples connect to each other, and all outside samples
  connect to each other.
- IF-BS-01 requires topological connectedness of the ambient closure space in
  order to infer that every nonempty proper region has nonempty boundary.

The Lean adapter makes these levels explicit. `C01Carrier` records admissible
states and transitions. `C01Connected` means that every two admissible states
are joined by a finite admissible transition path. The radial inside and outside
carriers satisfy this condition by IF-BS-18.

## Exact fit

For the radial finite chamber, take the C-01 state to be a grid sample, the
admissibility predicate to be `Inside` or its complement, and the transition to
be a predicate-preserving unit-grid step. The resulting two C-01 carriers are
formally connected.

This realizes the C-01 idea as a verified graph statement. It does not by
itself prove that an arbitrary world `X` is topologically connected.

## Red boundary

`C01TopologicalRealization.connectedness_transport` remains an explicit field
for arbitrary ambient realizations. The later module
`C01ReachabilityTopology.lean` discharges this seam for one canonical case: it
constructs a Kuratowski closure from C-01 reachability and proves
`C01Connected -> IsConnected` for that topology. Consequently IF-BS-01 needs no
additional connectedness assumption when its world is precisely this
admissible carrier equipped with the reachability topology.

The public caveat nevertheless remains necessary for an arbitrary ambient
space `X`. The reachability topology is defined on one admissible carrier; it
has not been identified with Euclidean closure or with a physical ambient
topology. A proper clopen component of a disconnected ambient space can still
have empty boundary. C-01 therefore closes the premise in its canonical model,
not universally.
