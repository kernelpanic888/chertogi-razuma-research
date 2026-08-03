# Passport: IF-BS-22F-B3C2B1

## Objective

Prove the real inequality required by the dominant-axis reverse-coverage construction before introducing finite-grid coordinate casts.

## Closed obligations

- A target-circle point has a coordinate of magnitude at least one.
- Inward rounding preserves sign-side magnitude and loses less than `1/m`.
- The orthogonal coordinate in the dominant branch has magnitude at most one.
- An adjacent inside/outside bracket plus affine interpolation has dominant-coordinate error at most `3/m`.

## Red boundary

The abstract real bracket has not yet been identified with the selected finite-grid crossing edge.

## Next point

IF-BS-22F-B3C2B2: define physical coordinates of grid samples, transport `Inside`, `outside`, adjacency and axis equalities into the real bracket lemma, identify the interpolation with `segmentRealPoint 0`, and combine coordinate errors into an explicit Euclidean bound.
