# IF-BS-22F-C: boundary separation invariant

## Concrete identity region

In canonical Euclidean two-space define

`A := ball(0, sqrt(2))`.

Its interface and exterior are

`Sigma := sphere(0, sqrt(2))`,

`E := complement(closedBall(0, sqrt(2)))`.

## Separation invariant

The checked invariant contains all of the following facts:

- `A`, `Sigma`, and `E` are nonempty;
- they are pairwise disjoint;
- every ambient point belongs to exactly one of the three roles;
- `Sigma` is compact;
- `frontier(A) = Sigma`.

Thus the boundary is not an extra decoration attached to an already complete object. It is the compact third role required to separate a proper inside from its outside in this connected Euclidean realization.

## Link to IF-BS-01

The region `A` is formally proper: it contains the origin and excludes an explicit exterior point. The standard topological identity

`frontier(ball(0,sqrt(2))) = sphere(0,sqrt(2))`

instantiates the boundary-of-self reading without taking connectedness as an opaque project-specific axiom.

## Link to the finite contour theorem

The target carrier built from the radial equation is proved equal to `Sigma`. Its canonical closure is still `Sigma`. For every `m>0`,

`hausdorffDist(K_m, frontier(A)) <= 4/m`,

and for any supplied anchor sequence,

`Filter.Tendsto (n -> hausdorffDist(K_(n+1), frontier(A))) atTop (nhds 0)`.

The finite computed contour therefore converges to the actual topological frontier of the concrete proper region.

## Honest boundary

This theorem concerns a specific radial region in Euclidean two-space. It supports the logical form of IF-BS-01, but it does not prove that every physical, biological, or conscious identity is represented by such a ball. It also does not identify `1/m` with the Planck scale.
