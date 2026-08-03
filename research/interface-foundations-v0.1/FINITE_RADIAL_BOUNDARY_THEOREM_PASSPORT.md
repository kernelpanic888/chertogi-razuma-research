# Passport: IF-BS-21

## Name

Complete finite radial boundary certificate.

## Closed chain

`inside/outside connectivity + threshold bond`

`local exact-two incidence + finite alternating traversal`

`orbit parity + rectangular potential + path separation`

`minimality -> every orbit is the complete geometric cut`

## Main result

`finite_radial_boundary_is_single_geometric_contour`

## Included evidence

- IF-BS-18 side connectivity
- IF-BS-19 bond
- IF-BS-20A inclusion minimality
- IF-BS-20B parity potential
- IF-BS-20C local orbit parity
- IF-BS-20D global marking
- IF-BS-20E orbit separation and completeness

## Claim boundary

Finite-grid geometric uniqueness is claimed. Continuous-limit convergence is
not claimed.

## Verification

- Main module: Lean 4.32.1 pass.
- Independent audit: Lean 4.32.1 pass.
- Source scan: no `axiom`, `sorry`, or `admit`.
- Final certificate reports only `propext`, `Classical.choice`, and
  `Quot.sound`.

## Next point

IF-BS-22: define the embedded polygonal contour and prove an explicit
Hausdorff-distance upper bound to the continuous radial boundary as a function
of `m`.
