# IF-BS-22F-B3C1: orbit crossing to local segment

## Result

Every oriented threshold crossing recorded by the selected global contour orbit determines a concrete active grid cell, one crossing side of that cell, and the exact interpolated local contour edge on that side.

For a target point `q` on the circle, choose the horizontal crossing facing the sign of `q.x`: the right crossing when `q.x >= 0`, otherwise the left crossing. IF-BS-22F-B3A/B places this crossing on the selected global orbit. IF-BS-22F-B3C1 then extracts its local segment and proves that the segment edge has exactly the same inner and outer samples as the selected oriented crossing.

## Formal route

`target point -> inward axis -> four axis crossings -> sign-facing crossing -> global orbit state -> active cell -> local segment edge`

## What is now closed

- The orbit witness is no longer merely combinatorial membership.
- Its cell-side incidence produces a concrete local polygonal segment.
- Edge orientation is normalized: the extracted edge's inner and outer samples equal the oriented crossing's samples.

## Honest boundary

This step does not yet bound the Euclidean distance from the original target-circle point to the extracted segment. That quantitative estimate is IF-BS-22F-B3C2.
