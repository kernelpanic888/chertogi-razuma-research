# IF-BS-22C: local segment radial bound

## Result

IF-BS-11 gives exactly two threshold-crossing sides in every active grid cell.
IF-BS-22C now parameterizes the segment joining their exact IF-BS-10 crossing
points and controls every rational point of that segment.

Let the two edge denominators be `d1` and `d2`, and put `D = d1 d2`. After
moving both endpoints to the common physical denominator `Dm`, let

- `Delta1` be the first endpoint's squared radial deficit;
- `Delta2` be the second endpoint's squared radial deficit;
- `S` be the squared common-numerator separation of the endpoints.

For a segment parameter `k/r`, with `0 <= k <= r`, Lean proves the exact
identity

`||P(k/r)||^2 = 2 - R/(r^2 D^2 m^2)`,

where

`R = r(r-k)Delta1 + rk Delta2 + k(r-k)S`.

The cell geometry and IF-BS-22B give

`Delta1 <= D^2`,

`Delta2 <= D^2`,

`S <= 2D^2`.

Consequently

`0 <= 2 - ||P(k/r)||^2 <= 3/m^2`.

The module also proves the positive-rational epsilon limit `3/m^2 -> 0`,
uniformly over the scale, the active cell, both segment vertices, and the
rational segment parameter.

## Formal mechanism

- Uncentered rational coordinates remove the common center translation.
- Every crossing point is proved to remain inside its source unit cell.
- Moving both endpoints to denominator `D` gives a squared separation at most
  `2D^2`.
- The exact two-dimensional chord identity supplies the segment correction.
- Endpoint corrections and the chord correction combine into one nonnegative
  residual bounded by `3/m^2`.

## Honest boundary

The theorem quantifies over every `UnitIntervalFraction`, hence over the full
rational trace of each local segment. It does not yet construct the real
completion of that trace or prove the statement for an arbitrary real
parameter. It also does not prove reverse coverage from the continuous circle
to the polygonal contour. A two-sided Hausdorff theorem is therefore not yet
claimed.
