# ITC-01 / Invariant Transport Closure

**Date:** 2026-08-22  
**Status:** machine-checked RC carrier · public formal-source seam open · live public reader  
**Author:** Salkutsan Aleksey Anatolievich  
**ORCID:** 0009-0006-8717-0492

## Result

The current model is recorded as a formal bridge:

\[
\text{persistence step}
=
\text{transition}
+
\text{invariant transport}.
\]

For a cyclic path \(\gamma : C_0 \leadsto C_0\), closure of the chosen invariant is recorded separately:

\[
\tau_\gamma(I(C_0)) = I(C_0).
\]

This return does not assert that \(\tau_\gamma = \mathrm{id}\), and the existence of a cycle does not prove dynamical stability.

## Two independent TLFL couplings

1. The growth contour uses a named transition \(g_D : C_t \to C_{t+1}\) together with transport \(\tau_g : I_D(C_t) \simeq I_D(C_{t+1})\).
2. The admissible-successor contour requires an explicit transition witness for the next state rather than static resemblance.

Boundary and stable record are connected as separate witnesses. They are not inferred from cyclic return.

## Public interface canon

The site now uses one visual-semantic invariant for its research chambers:

\[
\text{distinction} \to \text{transition} \to \text{trace} \to \text{return}.
\]

Every chamber inherits the same structural grammar while receiving a semantic voice: boundary, resource, carrier, corpus, identity, continuity, observation, poetry or transport. ITC-01 is the transport voice and therefore receives an orbit rather than a generic decoration.

## Interfaces

- [Live reader](https://chertogi-razuma-research.kernelpanic888.chatgpt.site/readers/invariant-transport-closure/)
- [Reader source](https://github.com/kernelpanic888/chertogi-razuma-research/blob/main/public/readers/invariant-transport-closure/index.html)
- [Lean/TLFL home](https://github.com/kernelpanic888/TMI-Lean-Formal-Library)
- [Corpus interface](https://chertogi-razuma-research.kernelpanic888.chatgpt.site/readers/corpus-interface/)

## External shoulders

- [Schreiber and Waldorf, Parallel Transport and Functors](https://arxiv.org/abs/0705.0452)
- [Kalinin, Livšic theorem for matrix cocycles](https://arxiv.org/abs/0808.0350)

These sources are shoulders for path transport and periodic-cocycle theory. They do not establish the present local-imbalance dynamics.

## Red boundary

The formal bridge does not prove that local imbalance produces an orbit, that a closed orbit is stable, or that return of one selected invariant makes the whole transport the identity. A concrete dynamics, a nontrivial closure theorem and an independent stability argument remain open obligations.

## Next seam

Freeze the dedicated public Lean source route and derive a nontrivial closed turn from an explicit local-imbalance dynamics.
