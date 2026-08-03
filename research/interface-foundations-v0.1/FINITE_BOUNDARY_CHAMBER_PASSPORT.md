# Passport IF-BS-03

Date: 2026-07-31
Object: a finite executable bridge from distinguishability to boundary.

## Inputs

- Carrier: Bool = {false, true}.
- Reference: false.
- Distinguishability: 0 on the diagonal, 2 off the diagonal.
- Resolution threshold: 1.
- Closure: empty stays empty; every nonempty region closes to the carrier.
- Adjacency: the two unequal points share the only edge.

## Checked outputs

1. The witness true is derived by computation: 1 < D(false,true).
2. X_eps(false) is exactly the singleton {true}.
3. X_eps(false) is a proper region.
4. The indiscrete closure satisfies the Kuratowski laws and is connected.
5. The frontier contains false and true.
6. The independently defined graph transition band contains false and true.
7. Lean proves frontier = PlanckTouchBand extensionally.

## Claim boundary

This is a finite model theorem, not an empirical Planck-scale measurement and
not a claim that spacetime has the chamber's topology.

## Next slice

Replace Bool by a finite path or grid with at least three resolution levels.
Compute the frontier under refinement and test whether the graph transition band
converges to a stable PlanckTouch candidate instead of coinciding only in a
two-point chamber.
