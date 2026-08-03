# IF-BS-22F-F8C21: exact tangent envelope

## Cancellation becomes structural

Let a point of the directional diamond be `(x,y,s)`, with `x^2+y^2=1`.
Write a tangent motion of the circle as

`(dx,dy)=theta*(-y,x)`

and the slope motion as `ds=sigma`. The product metric has infinitesimal norm

`max(|theta|,|sigma|)`.

For

`Phi_a(x,y,s)=x^2+(y+a s)^2`,

the raw differential simplifies exactly to

`dPhi_a=2a(x s theta+(y+a s)sigma)`.

The terms `2x dx+2y dy` cancel because the motion is tangent to the unit circle. Thus the full local variation vanishes identically when `a=0`.

## Exact dual norm at one point

Inside the unit max-box for `(theta,sigma)`,

`sup |dPhi_a|=2a(|x s|+|y+a s|)`.

Lean proves both the upper bound and attainment. The maximizing velocities are the signs of `x s` and `y+a s`.

## Exact compact reduction

Put `X=|x|`, `Y=|y|`. The diamond condition gives `|s|<=X+Y`.
For nonnegative amplitude,

`|x s|+|y+a s| <= X(X+Y)+Y+a(X+Y)`.

Every right-hand value is attained by the positive boundary record

`(x,y,s)=(X,Y,X+Y)`.

Therefore define

`E(a)=max { X(X+Y)+Y+a(X+Y) | X,Y>=0, X^2+Y^2=1 }`.

The quarter circle is compact, the displayed function is continuous, and Lean constructs an attaining maximizer. The exact local tangent modulus of the complete chamber is

`L_tan(a)=2a E(a)`.

## Honest boundary

`L_tan` is the exact infinitesimal modulus. It is not yet a proved global pairwise Lipschitz modulus for the ambient chord metric. A global theorem still needs either a path-to-chord comparison inside the diamond or a direct pairwise optimization.
