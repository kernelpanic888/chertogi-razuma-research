# IF-BS-22F-F8C18: exact slope envelope

## Exact attained slope radius

On the realizable directional diamond

`D = { (u,s) | |u| = 1 and |s| <= |u_x| + |u_y| }`,

the sheared slope component has the exact maximum

`R(a) = sqrt(a^2 + (1+a)^2)`,

`max_D |u_y + a s| = R(a)`.

The upper bound follows from the diamond endpoint and the two-dimensional Cauchy identity. Equality is attained by the normalized direction proportional to `(a,1+a)` with the reinforcing endpoint `s=u_x+u_y`.

## Improved forward modulus

The product metric on the blow-up chamber is

`d((u,s),(v,t)) = max(d(u,v), |s-t|)`.

Using the exact slope radius gives the proved global modulus

`L_slope(a) = 2 + 2(1+a)R(a)`.

For every nonnegative amplitude,

`L_slope(a) < L_2(a) = 2 + 4(1+a)^2`.

This strict comparison is uniform over the whole admissible chamber.

## Improved reciprocal certificate

The F8C17 exact spectral floor remains

`lambda_-(a) = 1-a+a^2-a sqrt((1-a)^2+1)`.

The new reciprocal modulus is

`L_inv,slope(a) = L_slope(a) / lambda_-(a)^2`.

It is strictly smaller than the F8C17 reciprocal modulus. For every positive mesh radius `delta`, the same exact finite sample supports

`0 <= Gamma_delta <= L_inv,slope(a) delta`.

At `a=1/2`,

`R=sqrt(5/2)` and `L_slope=2+3 sqrt(5/2) ~= 6.7434`,

while the former numerator was `11`. Thus the reciprocal mesh term contracts by about `38.7%` without changing the exact spectral denominator or the sample.

## Honest boundary

`R(a)` is an exact attained maximum. `L_slope(a)` is a strictly improved proved Lipschitz modulus, but it is not claimed to be the least possible pairwise constant: the spatial and slope component inequalities used in its construction may not be jointly sharp.
