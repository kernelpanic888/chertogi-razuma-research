# IF-BS-22F-B3A/B: inward circle-axis rounding

## Purpose

The four-axis theorem requires a row or column whose centre sample lies inside the radial threshold. B3A/B constructs such an axis from every real point of the target circle.

## Inward rule

For a real coordinate `u`, define

\[
k_m(u)=\lfloor m|u|\rfloor,
\qquad
a_m(u)=
\begin{cases}
2m+k_m(u),&u\ge 0,\\
2m-k_m(u),&u<0.
\end{cases}
\]

The absolute value is rounded down before the sign is restored. The selected grid coordinate therefore lies on the centre-facing side of the real coordinate. It cannot be rounded outward past a polar boundary.

The associated physical coordinate is

\[
\widehat u_m=
\operatorname{sgn}(u)\frac{\lfloor m|u|\rfloor}{m},
\qquad
|u-\widehat u_m|<\frac1m.
\]

## Interior guarantee

If `q=(x,y)` lies on the circle `x^2+y^2=2`, then

\[
|y|\le\sqrt2,
\qquad
\lfloor m|y|\rfloor^2\le 2m^2.
\]

Hence the row-centre sample `(2m,a_m(y))` satisfies the exact finite predicate `Inside`. The B1 least-outside scan is therefore available, and B2 generates right, left, top, and bottom oriented crossings from it.

## Global contour

IF-BS-21 places all four target-selected crossings on the complete global contour orbit. Thus every real target-circle point now selects certified finite threshold edges without assuming an unproved row-existence oracle.

## Honest boundary

This module bounds the selected axis-coordinate error and proves existence of finite crossings. It does not yet turn the orbit witness into a `LocalContourSegment`, choose the correct sign-facing crossing, or bound the Euclidean distance from the original circle point to the interpolated contour. Those are the B3C obligations.
