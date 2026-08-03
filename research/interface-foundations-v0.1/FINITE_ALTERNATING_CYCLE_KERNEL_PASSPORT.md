# Passport: IF-BS-14

## Name

Finite alternating successor and closed-cycle kernel.

## Question

Does alternating the two degree-two pairings force a finite contour state to return to itself?

## Objects

- A fixed-point-free involution for local segment pairing.
- A fixed-point-free involution for shared-edge pairing.
- Their successor and predecessor compositions.
- A finite list covering every traversal state.
- A self-contained orbit-prefix and pigeonhole construction.

## Formal claims

- Successor and predecessor are mutual inverses.
- An orbit prefix of length `N+1` in an `N`-state covered universe repeats.
- An inverse cancels the common prefix of a repeated orbit.
- Every state has a strictly positive period and therefore lies on a closed cycle.

## Verification rule

The main Lean module and separate import audit must compile. The audit reconstructs inverse laws, finite repetition, prefix cancellation, and the closed-cycle theorem. No `axiom`, `sorry`, or `admit` declaration is allowed.

## Verification result

Passed with Lean 4.32.1. The main module and independent audit compile. The source-gap scan is empty. `predecessor_successor` is axiom-free; the final finite closed-cycle theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Honest boundary

Proved: the finite cycle theorem for any explicitly covered alternating traversal.

Not proved here: construction of the concrete contour state enumeration and mate functions from IF-BS-11/IF-BS-13, connectedness of all cycle orbits, uniqueness of the radial component, planar Hausdorff convergence, or physical calibration.

## Next step

IF-BS-15: instantiate the kernel with the finite radial contour incidence space.
