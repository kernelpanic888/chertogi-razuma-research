# IF-BS-22F-F5: Finite controlled chains and bounded prefixes

## Finite theorem

An arbitrary finite list of controlled self-equivalences is folded into one
controlled chamber. If the forward constants are `L_0,...,L_(m-1)`, the folded
constant is exactly

`product_(i<m) L_i`.

The inverse constant is the product of all inverse constants. Concatenating two
lists acts as first traversing the first list and then the second. The resulting
computable boundary model satisfies

`d_H(F_chain[K_n],F_chain[I]) <= (product_i L_i)e_n`,

its interface is the actual frontier, and its error tends to zero.

## Prefix criterion

For an infinite sequence of controlled chambers, let

`P_n = product_(i<n) L_i`.

Every prefix is a valid finite controlled chamber. If one real constant `C`
satisfies `P_n <= C` for every `n`, then

`P_n e_n -> 0`.

Consequently, the Hausdorff error between the `n`th transported carrier and its
own `n`th transported interface tends to zero.

## Honest boundary

The target interface may move with `n`. The theorem proves vanishing error to
each moving actual frontier; it does not yet prove that those frontiers converge
to one common limiting set. A common-limit theorem needs additional Cauchy or
uniform convergence data for the transformations themselves.
