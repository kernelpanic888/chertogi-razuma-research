# IF-BS-20E: contour orbit separates

## Path transport

Every unit-adjacent primal edge has one canonical horizontal or vertical grid
representation. The orbit potential changes across an edge exactly when that
geometric edge is represented by the contour orbit.

A `CutAvoidingStep` either remains on one threshold side or uses a crossing not
contained in the orbit cut. In both cases the edge is unmarked and preserves
the Boolean potential. Every finite avoiding path therefore preserves colour.

## Separation

The anchor contour state supplies one orbit-marked crossing edge, whose inside
and outside endpoints have opposite colours. IF-BS-18 connects every inside
sample to the inside endpoint and every outside sample to the outside endpoint
without crossing the threshold. Those paths preserve colour.

Hence every inside sample and every outside sample have opposite orbit colours,
so no orbit-cut-avoiding path can join them:

`SeparatesSides (OrbitCut (SelectedOrbit hm anchor))`.

## Completeness

IF-BS-20A says every separating crossing subcut is the complete threshold cut.
Therefore the geometric edge set represented by any selected IF-BS-15 orbit
contains every threshold-crossing edge. This proves uniqueness of the radial
geometric contour component.

## Red boundary

The theorem concerns the finite sampled radial contour and its exact
interpolated edge incidences. It is not yet a Hausdorff-convergence theorem for
the continuous Euclidean circle as `m` tends to infinity.
