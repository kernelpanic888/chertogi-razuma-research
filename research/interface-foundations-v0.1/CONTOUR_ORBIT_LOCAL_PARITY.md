# IF-BS-20C: local parity of one contour orbit

## Orbit

The orbit of an IF-BS-15 contour state is closed under both the alternating
successor and its inverse predecessor. This removes any dependence on a chosen
direction or starting index.

An edge is marked by the orbit when either of its two cell-side incidence
states belongs to that orbit.

## Local theorem

If one side of a cell is marked, the alternating local/shared mate construction
marks the other threshold-crossing side of that cell. IF-BS-11 proves that an
active radial cell has exactly two crossing sides. Therefore every cell has
either no marked sides or exactly two marked sides.

The corresponding Boolean xor around every cell is zero.

## Consequence

This supplies the local hypothesis required by IF-BS-20B. The remaining bridge
is representational: package the four canonical cell sides as one global
horizontal/vertical edge marking and transport the resulting vertex potential
to `CutAvoidingStep` paths.

## Red boundary

Global edge-coordinate compatibility and the final separation theorem are not
claimed in this module.
