# IF-BS-22F-B3C2B2A: grid-to-physical coordinate adapter

## Normalization

For a grid sample `(i,j)` at resolution `m`, define:

`X=(i/m)-2`, `Y=(j/m)-2`.

The grid centre `(2m,2m)` becomes `(0,0)`, and one grid edge has physical length `1/m`.

## Transported facts

- The squared physical radius is exactly `radialNumerator/m^2`.
- A discrete `Inside` sample has physical squared radius at most two.
- A discrete outside sample has physical squared radius strictly greater than two.
- Right, left, up, and down unit grid steps become signed physical steps of exactly `1/m`.
- The inward-rounded target row and column become exactly the real coordinates used in the metric prelude.

## Honest boundary

The interpolated crossing point still has to be identified with the endpoint representation used by `segmentRealPoint`.
