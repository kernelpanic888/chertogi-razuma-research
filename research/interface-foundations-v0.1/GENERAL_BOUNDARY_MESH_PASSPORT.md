# Passport IF-BS-05

Date: 2026-07-31
Object: a general mesh theorem for a persistent shrinking threshold band.

## Inputs

- Mesh G_n with n edges and n+1 nodes.
- Internal threshold index k<n.
- Admission rule k<i.
- Crossing rule: neighbouring endpoint states differ.
- Normalized cell width Delta_n=1/n.

## Checked outputs

1. Edge i crosses if and only if i=k.
2. The band is exactly the endpoint pair {k,k+1}.
3. Both endpoint nodes belong to the band.
4. The endpoints are distinct.
5. The index width is exactly one cell.
6. Refinement makes unit-cell width antitone.
7. For every reciprocal target 1/m, all meshes n>=m have width at most 1/m.

## Claim boundary

The Lean theorem uses natural indices and a reciprocal-scale order. Full
real-valued epsilon convergence and metric-space convergence remain open.

## Next slice

Embed G_n into a declared rational or real metric interval. Prove the standard
epsilon-N limit for Delta_n and then extend localization from a monotone path to
a two-dimensional finite grid with a curved level-set boundary.
