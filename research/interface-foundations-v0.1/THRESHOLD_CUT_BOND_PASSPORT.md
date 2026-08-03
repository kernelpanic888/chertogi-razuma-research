# Passport: IF-BS-19

## Name

Threshold crossing cut as a finite graph bond.

## Question

Is the complete set of radial threshold-crossing edges a minimal inside/outside cut?

## Objects

- Predicate-free finite step reachability.
- Noncrossing inside/outside steps.
- Canonically oriented crossing edges.
- Reachability with one selected bridge restored.
- A bond certificate containing separation and essentiality.

## Formal claims

- Every noncrossing path preserves inside membership.
- No noncrossing path joins an inside point to an outside point.
- Restoring any one crossing edge reconnects arbitrary points on the two sides.
- The complete threshold crossing set is a bond.

## Verification rule

The main Lean module and independent import audit must compile. The audit reconstructs separation, one-edge restoration, and the bond certificate. No `axiom`, `sorry`, or `admit` declaration is allowed.

## Verification result

- Main module: Lean 4.32.1 pass.
- Independent audit: Lean 4.32.1 pass.
- Source scan: no `axiom`, `sorry`, or `admit`.
- Noncrossing separation and orientation existence are axiom-free.
- The selected raw orientation uses `Classical.choice`; the strengthened
  `orientCrossing_spec` proves that it orients the supplied edge.
- The bond certificate reports only `propext`, `Classical.choice`, and
  `Quot.sound`.

## Honest boundary

Proved here: the non-planar graph-theoretic bond property.

Not proved here: planar grid duality, connectedness of the medial contour, or uniqueness of the IF-BS-15 cycle.

## Next step

IF-BS-20: finite rectangular-grid bond-to-cycle duality.
