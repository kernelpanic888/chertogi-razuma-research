# ITC-01 / Invariant Transport Closure

**Date:** 2026-08-22  
**Status:** kernel-checked formal bridge · exact Lean commit frozen · release candidate, no DOI or tag<br>
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
- [Lean 4 source · commit 74a2a806](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/74a2a806a229830c668e66be233de2fda7bfc944/lean/TMI/InvariantTransportClosure.lean)
- [Axiom audit · same commit](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/74a2a806a229830c668e66be233de2fda7bfc944/lean/TMI/InvariantTransportClosureAudit.lean)
- [Formal source map and claim passport](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/74a2a806a229830c668e66be233de2fda7bfc944/research/invariant-transport-closure-v0.1/README.md)
- [Corpus interface](https://chertogi-razuma-research.kernelpanic888.chatgpt.site/readers/corpus-interface/)

## External shoulders

- [Schreiber and Waldorf, Parallel Transport and Functors](https://arxiv.org/abs/0705.0452)
- [Kalinin, Livšic theorem for matrix cocycles](https://arxiv.org/abs/0808.0350)

These sources are shoulders for path transport and periodic-cocycle theory. They do not establish the present local-imbalance dynamics.

## Red boundary

The formal bridge does not prove that local imbalance produces an orbit, that a closed orbit is stable, or that return of one selected invariant makes the whole transport the identity. A concrete dynamics, a nontrivial closure theorem and an independent stability argument remain open obligations.

## Build boundary

The dedicated ITC module and its audit build successfully with Lean 4.31.0-rc1. The existing experimental `MemoryGoalField.lean` source-level coupling is exact, but that file imports Mathlib while the current package manifest declares no Mathlib dependency; this RC does not misreport it as a compiled import.

## Next seam

Derive a nontrivial closed turn from an explicit local-imbalance dynamics, then prove stability independently. DOI assignment, a release tag and production deployment remain human release gates.
