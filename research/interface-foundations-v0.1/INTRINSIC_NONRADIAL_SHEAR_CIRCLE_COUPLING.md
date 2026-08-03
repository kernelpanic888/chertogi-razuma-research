# IF-BS-22F-F8C19: circle coupling

## The lost unit

F8C18 bounded the spatial square by the generic coordinate estimate

`|u_x^2-v_x^2| <= 2 d(u,v)`.

On the unit circle the two coordinates are coupled. F8C19 proves the stronger identity-driven bound

`|u_x^2-v_x^2| <= d(u,v)`.

For two distinct directions the inequality is strict:

`u != v -> |u_x^2-v_x^2| < d(u,v)`.

The proof uses the sum and difference vectors. Their orthogonality and the unit constraints imply a coupled quadratic bound that cannot reach equality at positive distance.

## Improved full modulus

Retaining the exact F8C18 slope radius

`R(a)=sqrt(a^2+(1+a)^2)`,

the new forward modulus is

`L_circle(a)=1+2(1+a)R(a)`.

It is exactly one unit below the F8C18 numerator and strictly below it for every amplitude. Moreover every distinct pair satisfies a strict version of the final forward inequality, so the factorized upper bound is never attained by a finite pair.

## Reciprocal and finite transfer

With the F8C17 exact lower spectral edge `lambda_-(a)`,

`L_inv,circle(a)=L_circle(a)/lambda_-(a)^2`.

The reciprocal regularity and every positive-radius mesh term are strictly smaller than F8C18. The existing exact finite sample therefore supports

`0 <= Gamma_delta <= L_inv,circle(a) delta`.

At `a=1/2`,

`L_circle=1+3sqrt(5/2) ~= 5.7434`.

This is about `14.8%` below F8C18 and `47.8%` below the original numerator `11`.

## Honest boundary

F8C19 proves strict non-attainment for every distinct pair. It does not yet prove whether the supremum of the circle ratio is exactly one, nor whether the complete coupled modulus is the least global Lipschitz constant. A strict pointwise inequality may still have the same constant as its asymptotic supremum.
