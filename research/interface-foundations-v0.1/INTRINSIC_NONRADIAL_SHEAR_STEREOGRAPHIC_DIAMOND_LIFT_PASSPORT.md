# PASSPORT / IF-BS-22F-F8C31B

## Claim

Two explicit rational charts from Bool x [-1,1] x [-1,1] are jointly surjective onto directionalDiamondBand.

## Direct map

D(h,t,v) = (d_h(t), v (|d_h(t)_x|+|d_h(t)_y|))

with d_true(t)=((1-t^2)/(1+t^2), 2t/(1+t^2)) and d_false(t)=(-(1-t^2)/(1+t^2), 2t/(1+t^2)).

## Verified

- every chart direction has unit Euclidean norm;
- every chart width is positive and at most sqrt(2);
- every lift with v in [-1,1] belongs to the exact directional diamond;
- every exact-diamond point has an east or west inverse parameter;
- the inverse fiber parameter belongs to [-1,1];
- the reconstructed lift is exactly the original point.

## Honest boundary

F8C31B proves coverage as a set-theoretic and algebraic statement. It does not yet provide a global numerical Lipschitz constant for the lift or the resulting ambient delta-net radius.

## Next

F8C31C: bound the chart derivatives on [-1,1], bound the width/fiber term, and derive an explicit BlowUpPoint distance from parameter max-distance.
