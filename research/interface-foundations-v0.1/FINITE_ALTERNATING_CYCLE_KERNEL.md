# IF-BS-14: finite alternating cycle kernel

## Traversal

A contour traversal alternates two pairings on one finite state space:

- `localMate`: move to the other exact vertex of the same IF-BS-11 segment;
- `sharedMate`: move to the representation of that vertex in the neighbouring IF-BS-13 cell.

Both pairings are fixed-point-free involutions. Their composition is the successor

`successor = shared o local`,

with explicit inverse

`predecessor = local o shared`.

Lean proves both inverse equations exactly.

## Finite closure

The module does not import a graph or pigeonhole library. It proves directly that a duplicate-free list cannot be longer than a covering finite list. Therefore the first `N+1` states of any orbit in an `N`-state finite cover contain a repetition.

For an invertible successor, a repetition after a shared prefix can be cancelled with the predecessor. Every starting state consequently has a positive period `p` satisfying

`successor^p(x) = x`.

Thus every state of a finite alternating traversal lies on a closed cycle, not merely on an eventually periodic tail.

## Verification

The main module and the independent audit compile with Lean 4.32.1. The source-gap scan finds no `axiom`, `sorry`, or `admit`. The inverse law is axiom-free; the finite-list and closed-cycle theorems report only Lean's standard logical dependencies: `propext`, `Classical.choice`, and `Quot.sound`.

## Red boundary

This is the fully verified finite cycle-extraction kernel. IF-BS-11 and IF-BS-13 provide the required local and shared exact-two facts, but the concrete global contour state type and its two executable mate functions are not yet instantiated in this module.

## Next

IF-BS-15 should define the finite contour-incidence state space, instantiate both involutions from the existing exact-two certificates, and apply the kernel without additional graph assumptions.
