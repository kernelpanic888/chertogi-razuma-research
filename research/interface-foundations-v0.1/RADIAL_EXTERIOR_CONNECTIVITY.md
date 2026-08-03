# IF-BS-17: radial exterior connectivity

## Canonical outward route

For each outside sample, the x-direction away from the centre is selected deterministically. The first segment reaches either the left or right vertical frame while never decreasing radial distance.

The second segment follows that vertical frame to the bottom edge. The third follows the bottom frame to the common corner `(0,0)`.

## Exterior certificate

Every intermediate integer sample on all three segments is outside. Thus every sampled exterior point reaches one common outer-frame point without crossing the sampled inside disk.

## Verification

The main module and independent audit compile with Lean 4.32.1, and the source-gap scan is empty. The complete outward path theorem reports only `propext` and `Quot.sound`; no `Classical.choice` is used.

Together with IF-BS-16, both sides of the radial distinction now have explicit connectivity carriers: the inside reaches the centre and the outside reaches the common frame corner.

## Red boundary

This does not by itself identify the polygonal incidence traversal with the boundary of those two connected sample regions. A final finite planar-separation bridge is required before claiming that the IF-BS-15 family of cycles contains exactly one cycle.

## Next

IF-BS-18 should prove the finite grid separation bridge: two or more disjoint degree-two contour cycles would force an additional inside or outside component, contradicting IF-BS-16 or IF-BS-17.
