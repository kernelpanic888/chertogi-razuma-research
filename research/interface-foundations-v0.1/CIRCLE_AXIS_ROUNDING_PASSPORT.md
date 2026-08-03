# Passport IF-BS-22F-B3A/B

## Name

Inward rounding and certified target axes.

## Inputs

- A real point on the target circle `x^2+y^2=2`.
- A positive finite-grid scale `m`.
- IF-BS-22F-B1 rightward threshold bracketing.
- IF-BS-22F-B2 exact axis symmetries.
- IF-BS-21 completeness of the global contour orbit.

## Outputs

- A computable inward offset `floor(m*|u|)`.
- A signed grid axis in the interval `[0,4m]`.
- Coordinate approximation error strictly below `1/m`.
- Exact proof that the selected row-centre sample is `Inside`.
- Four oriented threshold crossings for every target-circle point.
- Membership of all four crossings in the complete global contour orbit.

## Verification

- Main verification target: `formal/CircleAxisRounding.lean` under Lean 4.32.1.
- Independent audit target: `formal/CircleAxisRoundingAudit.lean`.
- Source gate: no declaration using `axiom`, `sorry`, or `admit` is permitted.

## Red boundary

- The correct sign-facing crossing has not yet been selected from the four-axis certificate.
- Orbit membership has not yet been unpacked into a local segment and endpoint parameter.
- The reverse Euclidean estimate and `ReverseCoverageMesh` remain open.
- No physical identification of the finite radial grid is claimed.

## Next point

IF-BS-22F-B3C: select the right or left crossing from the sign of the target coordinate, extract its local contour segment from the orbit witness, and prove a quantitative circle-to-contour distance bound.
