# IF-BS-22F-F8C16: exact-domain finite certificates

## Domain transport

F8C15 identifies the exact compact chamber of finite-chord blow-ups:

`closure(records)=D`,

`D={(u,s) | |u|=1 and |s|<=|u_x|+|u_y|}`.

F8C16 moves the finite forward and inverse delta-net certificates from the larger relaxed strip onto `D` itself.

## A second lower square certificate

Write

`Phi_a(u,s)=u_x^2+(u_y+a s)^2`.

For `0<=a<1` and `(u,s) in D`, the directional constraint implies

`(1-a)|u_y| <= |u_y+a s| + a|u_x|`.

After squaring, applying `(r+t)^2<=2r^2+2t^2`, and using `u_x^2+u_y^2=1`, Lean verifies

`(1-a)^2/2 <= Phi_a(u,s)`.

Define

`lambda_D(a)=max((1-sqrt(2)a)^2,(1-a)^2/2)`.

Both entries are independently proved lower bounds on `D`, so their maximum is also a lower bound. It can never be weaker than the relaxed certificate.

## Improved inverse modulus

The forward regularity modulus remains

`L_2(a)=2+4(1+a)^2`.

The inverse modulus on the exact chamber is now certified by

`L_inv,D(a)=L_2(a)/lambda_D(a)^2`.

Since `lambda_D(a)>=(1-sqrt(2)a)^2`, Lean proves

`L_inv,D(a)<=L_inv,relaxed(a)`.

Consequently, for every `delta>=0`,

`L_inv,D(a) delta <= L_inv,relaxed(a) delta`.

At `a=1/2`, the new diamond bound is `1/8`, strictly larger than the relaxed bound `(1-sqrt(2)/2)^2`. Therefore every positive-mesh inverse error term is strictly smaller. Numerically, `L_2(1/2)=11`: the old modulus is about `1494.7`, while the certified diamond modulus is `704`.

## Finite certificates on the exact chamber

Compactness of `D` gives finite exact delta-nets for both observables. Lean constructs:

- a forward sample with `Phi_a(point)<=sampleMax+L_2(a)delta` for every point of `D`;
- an inverse sample with `Phi_a(point)^-1<=sampleMax+L_inv,D(a)delta` for every point of `D`.

The sampling domain now equals the realizable closure rather than merely containing it.

## Honest boundary

`lambda_D` is a certified hybrid lower bound, not yet claimed to be the sharp minimum of `Phi_a` on `D`. The exact spectral envelope and a sharp regularity modulus remain separate optimization problems.
