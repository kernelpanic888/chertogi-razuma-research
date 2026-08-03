# IF-BS-20B: rectangular parity potential

## Discrete Poincare lemma

Mark horizontal and vertical edges of a finite rectangular grid by Boolean
values. Assume that the xor of the four marks around every cell is zero.

Choose the lower-left vertex as origin. Define the colour of `(x,y)` by the
xor accumulated first along the bottom row and then up column `x`.

Cell parity proves path independence in the required local form. The resulting
potential satisfies

`color(x,y) xor color(x+1,y) = horizontal(x,y)`

`color(x,y) xor color(x,y+1) = vertical(x,y)`.

Thus every marked edge has endpoints of opposite colour. Any path made only of
unmarked, hence colour-preserving, steps cannot join those endpoints.

## Role in digital Jordan separation

This replaces an imported visual Jordan intuition with a finite algebraic
certificate. Once one closed IF-BS-15 contour orbit is converted into a marking
whose incidence in every cell is zero modulo two, the potential proves that
the orbit's edges form a primal separating cut. IF-BS-20A then forces that orbit
to contain every threshold crossing.

## Red boundary

The parity-to-potential theorem is proved here. The remaining instantiation is
to show that an IF-BS-15 successor orbit marks both sides of each visited local
segment and therefore has even cell incidence.
