# IF-BS-22F-F8C13: inverse blow-up and exact relaxed poles

## Question

F8C12 turned every nonzero chord into a point of the compact relaxed chamber

`C = S^1 x [-sqrt(2),sqrt(2)]`

and encoded squared forward stretch by

`Phi_a(u,s)=u_x^2+(u_y+a s)^2`.

F8C13 asks when this record is safely invertible, where its exact relaxed poles lie, and how far a finite certificate can sit above the exact inverse pole.

## Admissible amplitude

The chamber remains uniformly separated from zero under

`0 <= a` and `sqrt(2)a < 1`.

This is a theorem about the relaxed chamber, not a physical threshold claim.

## Exact relaxed envelopes

Every `(u,s) in C` satisfies

`(1-sqrt(2)a)^2 <= Phi_a(u,s) <= (1+sqrt(2)a)^2`.

Both bounds are attained inside `C`:

- lower pole: `u=(0,1)`, `s=-sqrt(2)`;
- upper pole: `u=(0,1)`, `s=+sqrt(2)`.

Thus these are exact extrema of the relaxed chamber.

## Inverse observable

Define

`Psi_a(u,s)=1/Phi_a(u,s)`.

Then

`(1+sqrt(2)a)^(-2) <= Psi_a(u,s) <= (1-sqrt(2)a)^(-2)`.

The reciprocal observable is regular on `C` with explicit safe modulus

`L_inv(a) = [2+4(1+a)^2] / (1-sqrt(2)a)^4`.

## Finite inverse certificate

For every `delta>0`, a finite exact sample of `C` gives

`Psi_a(x) <= M_N + L_inv(a) delta`.

Relative to the exact relaxed inverse pole, define

`Gamma_delta = M_N + L_inv(a)delta - (1-sqrt(2)a)^(-2)`.

The formal result proves

`0 <= Gamma_delta <= L_inv(a)delta`.

The finite excess therefore vanishes linearly with the mesh radius.

## Honest boundary

The two poles are exact for the relaxed outer chamber. F8C13 does not prove that both pole records are realized by finite physical chords of the intrinsic tent shear. The difference between the relaxed chamber and the closure of realizable chord records remains open.

