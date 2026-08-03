# IF-BS-22F-F8C17: sharp spectral envelope

## Exact chamber

For an admissible amplitude `0 <= a < 1`, consider

`D = { (u,s) | |u| = 1 and |s| <= |u_x| + |u_y| }`

and

`Phi_a(u,s) = u_x^2 + (u_y + a s)^2`.

The exact spectral edges on `D` are

`lambda_-(a) = 1 - a + a^2 - a sqrt((1-a)^2 + 1)`,

`lambda_+(a) = 1 + a + a^2 + a sqrt((1+a)^2 + 1)`.

The Lean carrier proves both global inequalities and explicit normalized witnesses attaining equality. Thus these constants are not estimates: they are the minimum and maximum of `Phi_a` on the exact directional diamond.

## Extremizing directions

A lower witness is obtained by normalizing

`(1-a, 1 + sqrt((1-a)^2 + 1))`

and taking the cancelling endpoint `s = -(u_x+u_y)`.

An upper witness is obtained by normalizing

`(1+a, 1 + sqrt((1+a)^2 + 1))`

and taking the reinforcing endpoint `s = u_x+u_y`.

## Sharp reciprocal certificate

Because `lambda_-(a) > 0`, the inverse observable is bounded by

`lambda_+(a)^(-1) <= Phi_a(u,s)^(-1) <= lambda_-(a)^(-1)`.

The exact lower edge replaces the hybrid F8C16 denominator in the reciprocal regularity modulus:

`L_sharp(a) = L_2(a) / lambda_-(a)^2`.

A finite exact delta-net exists on `D`. Its global inverse certificate has a gap

`0 <= Gamma_delta <= L_sharp(a) delta`.

At `a=1/2`, `lambda_- = (3-sqrt(5))/4 ~= 0.190983`, strictly above the F8C16 certified lower `1/8`. Hence both the sharp reciprocal regularity and every positive-radius mesh term are strictly smaller than the previous certified values.

## Honest boundary

The spectral denominator is now exact. The numerator still uses the coarse forward Lipschitz modulus `L_2(a)`; F8C17 does not claim that this regularity constant is optimal. No physical interpretation is inferred from the mathematical certificate.
