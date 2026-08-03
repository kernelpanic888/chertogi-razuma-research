# Passport: IF-BS-09

## Name

Uniform radial boundary family.

## Question

Can the finite 17x17 boundary chamber be replaced by a theorem valid at every positive resolution?

## Objects

- Scale `m > 0`.
- Grid side `4m+1`.
- Centre `(2m,2m)`.
- Radial numerator `F_m(x,y) = |x-2m|^2 + |y-2m|^2`.
- Threshold `T_m = 2m^2`.
- Unit-adjacent crossing edge.

## Formal claims

- A unit step changes `F_m` by at most `4m+1`.
- `4m+1 <= 5m` for every `m > 0`.
- Both endpoints of every crossing edge satisfy `|F_m-T_m| <= 5m`.
- The normalized squared-radius width `5/m` is below every positive rational epsilon at sufficiently large `m`.
- The case `m=4` is exactly compatible with the IF-BS-08 numerator.

## Verification rule

The main module must compile with Lean 4. The audit module must reconstruct the claims through the public theorem surface and print their axiom dependencies. The source must contain no `axiom`, `sorry`, or `admit` declarations.

## Verification result

- Lean 4.32.1 accepts the main module and the separate import audit.
- The source gap scan is clean.
- `normalized_band_limit` and the `m=4` bridge report only `propext` and `Quot.sound`.
- The adjacency and crossing-band theorems additionally report `Classical.choice` through the imported finite-grid infrastructure.

## Status boundary

Proved: a resolution-independent arithmetic estimate and rational convergence of the squared-radius residual.

Not proved: Euclidean distance to the circle, an interpolated contour, Hausdorff convergence, continuum physics, or a physical Planck limit.

## Next step

IF-BS-10: define the interpolated contour and derive a metric radial localization theorem before using the word Hausdorff.
