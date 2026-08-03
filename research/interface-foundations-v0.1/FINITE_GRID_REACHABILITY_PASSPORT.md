# Passport: IF-BS-18

## Name

Finite unit-grid reachability for both radial regions.

## Question

Do the axis-segment certificates correspond to genuine paths in the unit-adjacency graph?

## Objects

- Predicate-preserving unit-edge reachability.
- Finite horizontal and vertical path recursion.
- The inside centre path.
- The outside frame-corner path.

## Formal claims

- Reachability is symmetric and transitively composable.
- Every certified integer axis segment realizes a finite unit-edge path.
- Any two inside samples are connected through the centre.
- Any two outside samples are connected through the common frame corner.

## Verification rule

The main Lean module and independent import audit must compile. The audit reconstructs both global pairwise-connectivity theorems. No `axiom`, `sorry`, or `admit` declaration is allowed.

## Verification result

Passed with Lean 4.32.1. The main module and independent audit compile, and the source-gap scan is empty. Both final connectivity theorems report only `propext`, `Classical.choice`, and `Quot.sound`.

## Honest boundary

Proved here: exact graph connectivity of both complementary sampled regions.

Not proved here: finite planar duality or uniqueness of the concrete medial contour cycle.

## Next step

IF-BS-19: rectangular-grid cut duality and one-cycle uniqueness.
