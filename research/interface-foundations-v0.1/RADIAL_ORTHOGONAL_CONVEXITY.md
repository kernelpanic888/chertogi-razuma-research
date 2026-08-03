# IF-BS-16: radial orthogonal convexity

## Arithmetic carrier

The sampled radial field is monotone in both absolute coordinate offsets from the centre. Reducing either offset cannot turn an inside sample into an outside sample; increasing both offsets cannot turn an outside sample into an inside sample.

## Interval theorem

For any fixed row, every integer sample between two inside samples is inside. The same holds for every fixed column. Thus horizontal and vertical slices of the sampled disk contain no gaps.

## Centre connection

Every inside sample admits a certified L-shaped connection to the exact centre. The horizontal segment reaches the centre column and the vertical segment then reaches the centre sample. Every intermediate integer sample on both segments remains inside.

## Verification

The main module and independent audit compile with Lean 4.32.1, and the source-gap scan is empty. Radial-numerator monotonicity is axiom-free. The interval and centre-connection theorems report only `propext` and `Quot.sound`, with no `Classical.choice`.

## Meaning

The interior is not merely nonempty. It is orthogonally star-connected to the centre and cannot split into two sampled components.

## Red boundary

This is the arithmetic connectivity half of contour uniqueness. A separate finite planar-separation theorem is still required to derive that the degree-two boundary traversal consists of exactly one cycle. The exterior connectivity and the final incidence-to-separation bridge are not claimed here.

## Next

IF-BS-17 should prove the outward connectivity of the sampled exterior and combine both connectivity certificates with IF-BS-15 to rule out multiple boundary cycles.
