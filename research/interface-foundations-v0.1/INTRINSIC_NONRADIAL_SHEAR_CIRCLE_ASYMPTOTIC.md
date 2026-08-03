# IF-BS-22F-F8C20: asymptotic circle witness

## The missing endpoint

F8C19 proves that every distinct pair of unit directions satisfies

`|u_x^2-v_x^2| < d(u,v)`.

F8C20 supplies the explicit symmetric family

`P_t=((1+t),(1-t))/sqrt(2(1+t^2))`,

`Q_t=((1-t),(1+t))/sqrt(2(1+t^2))`.

For `t>0`, the points are distinct and lie on the unit circle. Lean verifies

`P_t.x^2-Q_t.x^2 = 2t/(1+t^2)`,

`d(P_t,Q_t)^2 = 4t^2/(1+t^2)`.

Therefore

`|P_t.x^2-Q_t.x^2|/d(P_t,Q_t)=1/sqrt(1+t^2)`,

which approaches `1` as `t` approaches zero. The constant `1` is thus the least global coefficient, although no distinct pair attains equality.

## Lift into the directional diamond

Lift each direction with its positive edge slope:

`s(P_t)=P_t.x+P_t.y`, `s(Q_t)=Q_t.x+Q_t.y`.

Both records lie in the directional diamond for `0<=t<=1`, and their slopes are exactly equal. The lifted distance is unchanged.

For the full forward chamber `Phi_a`, Lean verifies the exact cancellation

`Phi_a(P_t,s)-Phi_a(Q_t,s)=-4at/(1+t^2)`.

The circle witness is sharp for the isolated `x^2` term, but the swapped `y^2` term cancels it and the common slope removes the slope difference. Its full ratio approaches `2a`, not the factorized F8C19 modulus.

## Consequence

F8C20 closes the sharpness question for the isolated circle coefficient. It also rules out this natural witness family as a joint extremizer of the complete forward estimate.

## Honest boundary

This cancellation does not determine the least global Lipschitz constant of the complete chamber. The next optimization must use admissible tangent directions of the full directional diamond and the max product metric rather than adding independently sharp component bounds.
