# Passport: IF-BS-22F-B3C2A

## Objective

Replace the horizontal-only sign selector with a pole-stable dominant-axis selector before deriving reverse Euclidean coverage.

## Construction

`swapTarget(x,y)=(y,x)` preserves the target circle. Build one crossing family from the original target and a second family from the swapped target.

The selector is:

`|y| <= |x|  ->  horizontal right/left by sign(x)`

`|x| < |y|   ->  vertical top/bottom by sign(y)`

## Closed obligations

- Coordinate swap preserves the target circle.
- Vertical sign selection has the correct fixed column and direction.
- The dominant selector chooses one of the two certified families.
- Every selected crossing belongs to the same global orbit.
- Every selected crossing produces a concrete local segment through IF-BS-22F-B3C1.

## Red boundary

The theorem does not yet state the value of the reverse-distance constant.

## Next point

IF-BS-22F-B3C2B: prove the dominant coordinate is at least one, derive a Lipschitz bound for the square-root radial coordinate, identify the extracted edge endpoint with its segment endpoint, and close `d(q,Gamma_m) <= C/m`.
