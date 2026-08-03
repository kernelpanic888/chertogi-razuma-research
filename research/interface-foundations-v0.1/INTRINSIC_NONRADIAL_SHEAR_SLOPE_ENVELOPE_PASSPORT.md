# Passport: IF-BS-22F-F8C18

## Node

Exact attained slope envelope and its transfer into forward and inverse finite certificates.

## Verified output

- `R(a)=sqrt(a^2+(1+a)^2)` is the exact maximum of `|u_y+a s|` on `D`.
- A normalized explicit witness proportional to `(a,1+a)` attains the maximum.
- `L_slope(a)=2+2(1+a)R(a)` is a global forward regularity modulus on `D`.
- `L_slope(a)` is strictly smaller than the former `L_2(a)` for every nonnegative amplitude.
- The corresponding reciprocal modulus and every positive-radius mesh term are strictly smaller than F8C17.
- A finite exact inverse sample exists with `0 <= Gamma_delta <= L_inv,slope(a) delta`.
- At `a=1/2`, the numerator contracts from `11` to `2+3sqrt(5/2)`, about `38.7%`.
- The carrier and audit contain no local `axiom`, `sorry`, or `admit`.

## Red boundary

The exact attained slope radius does not by itself prove that the factorized forward modulus is the least pairwise Lipschitz constant for the max product metric.

## Next passport step

`IF-BS-22F-F8C19`: solve the coupled pairwise optimization for the least Lipschitz constant of `Phi_a` on `D`, or prove a strict obstruction showing why the factorized component bounds cannot be attained simultaneously.
