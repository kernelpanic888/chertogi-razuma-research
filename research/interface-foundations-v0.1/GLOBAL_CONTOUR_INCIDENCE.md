# IF-BS-12: interior two-sided contour incidence

## Result

Canonical horizontal and vertical grid edges now carry their exact endpoint geometry. At positive scale, every node on the outer square has one radial offset equal to `2m`, so its radial numerator is strictly larger than the threshold `2m^2`.

Consequently an edge on the outer frame has two outside endpoints and cannot cross the threshold. Every crossing edge is therefore strictly interior:

- a horizontal crossing has `0 < y < 4m`;
- a vertical crossing has `0 < x < 4m`.

This produces two genuine neighbouring cells for every crossing edge. The horizontal case supplies the below/north and above/south incidences; the vertical case supplies the left/east and right/west incidences. Each cell is proved active and therefore carries the unique two-vertex IF-BS-11 segment.

## Meaning

The local contour can no longer terminate at the finite grid frame. Every exact contour vertex has a constructed continuation from each side of its underlying grid edge.

## Red boundary

This proves existence of the canonical two incident segments. A separate classification theorem must still prove that every cell-side representation of the same grid edge is one of these two. Only after that at-most-two result may the global degree be called exactly two and the finite contour be packaged as a closed mod-two 1-cycle.

## Next

IF-BS-13 should classify all incidences of a canonical grid edge, prove exact global degree two, and derive vanishing mod-two boundary.
