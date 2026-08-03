# IF-BS-22F-B1: finite axis threshold bracket

## Purpose

Reverse circle coverage requires a concrete threshold edge near a prescribed direction. IF-BS-22F-B1 proves the finite existence mechanism for a rightward horizontal scan.

## Scan

Fix a row `y` of the `4m x 4m` radial grid. Start at the horizontal center `x=2m` and scan right through offsets `k=0,...,2m`.

- `k=0` is the row center;
- `k=2m` is the right frame `x=4m`;
- the scan is clipped to this finite interval.

If the row center is inside the radial threshold, the right frame is outside whenever `m>0`. Therefore a least outside offset exists.

## Bracket theorem

Let `k` be the least outside offset. Lean proves:

- `0<k<=2m`;
- the sample at `k-1` is inside;
- the sample at `k` is outside;
- the two samples are unit-adjacent;
- together they form an `OrientedCrossing`.

The proof uses a finite witness at `k=2m` and minimality of `Nat.find`.

## Global orbit bridge

IF-BS-21 states that every oriented radial threshold crossing belongs to every selected complete contour orbit. Consequently the row crossing constructed here belongs to the unique global geometric contour.

## Honest boundary

This module currently constructs the rightward row crossing. Reflection supplies the left crossing; coordinate exchange supplies top and bottom crossings. The real rounding and distance estimate from an arbitrary circle point are not yet part of B1.
