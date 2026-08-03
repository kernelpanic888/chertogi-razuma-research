# IF-BS-20D: global contour-orbit marking

## Construction

Every horizontal or vertical grid edge is identified by its integer
coordinates. It is marked when an incidence state representing that geometric
edge belongs to the selected alternating contour orbit.

Coordinate uniqueness proves that the mark is independent of proof fields and
of the cell from which the edge is viewed.

## Cell compatibility

For every grid cell, the four global values coincide exactly with its local
`south`, `east`, `north`, and `west` orbit marks. IF-BS-20C therefore gives xor
zero around every cell.

The marking satisfies `ClosedOn` over the complete `4m x 4m` rectangle.
IF-BS-20B then constructs its global Boolean vertex potential.

## Red boundary

The potential exists and its edge gradients are proved. The next module must
classify arbitrary unit-adjacent primal steps and show that every step avoiding
the orbit cut preserves this potential.
