# IF-BS-22F-B3C2C: dominant-axis reverse coverage

## Theorem

For every resolution `m>0`, every selected global contour orbit, and every point `q` on the target circle, there is a real point `p` on a concrete local contour segment such that:

`d(q,p) <= 4/m`.

The witness is the exact threshold endpoint of the dominant-axis crossing and is represented as `segmentRealPoint 0 segment vertex vertex`.

## Branches

- `|x|>=|y|, x>=0`: right crossing.
- `|x|>=|y|, x<0`: left crossing.
- `|y|>|x|, y>=0`: top crossing.
- `|y|>|x|, y<0`: bottom crossing.

Each branch has dominant-coordinate error at most `3/m` and orthogonal-coordinate error at most `1/m`. Hence the squared Euclidean error is at most `10/m^2`, which is bounded by `(4/m)^2`.

## Bidirectional result

Together with IF-BS-22E, the finite contour and the target circle satisfy:

- contour to circle: `sqrt(3)/m`;
- circle to contour: `4/m`.

This is the first explicit two-sided Euclidean approximation theorem in the finite radial contour chain.

## Honest boundary

The theorem is a finite combinatorial and Euclidean convergence result for the constructed radial contour. It does not by itself establish a physical Planck scale or metaphysical claim.
