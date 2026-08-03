# IF-BS-22F-B2: exact axis symmetries

## Purpose

IF-BS-22F-B1 constructs one inside-to-outside threshold edge by scanning right from a row centre. B2 proves that one finite search is enough for all four axial directions.

## Exact symmetries

On the `4m+1` radial grid, Lean defines

\[
R_x(x,y)=(4m-x,y),
\qquad
S(x,y)=(y,x).
\]

Both operations are involutions. They preserve the squared radial numerator, and therefore preserve the threshold predicate `Inside`. They also preserve unit-grid adjacency. Consequently they send an oriented inside-to-outside crossing to another oriented inside-to-outside crossing.

## Four-axis theorem

For every admissible axis coordinate whose central row sample lies inside the radial threshold, the B1 rightward edge generates:

- a right crossing with increasing `x`;
- a left crossing with decreasing `x`;
- a top crossing with increasing `y`;
- a bottom crossing with decreasing `y`.

IF-BS-21 then places all four crossings on the same complete global contour orbit.

## Meaning

The construction is not four repeated least-witness searches. It is one finite threshold bracket transported through exact automorphisms of the discrete radial model. This removes directional bias from the B1 construction.

## Honest boundary

The theorem controls the four axial directions attached to a chosen row/column. It does not yet choose a safe integer row from an arbitrary real point of the target circle. It also does not yet prove a reverse Euclidean distance bound or full angular coverage. Those remain the next quantitative layer.
