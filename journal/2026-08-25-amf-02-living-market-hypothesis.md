# AMF-02 / Living Market Hypothesis Steward

Date: 2026-08-25  
Status: executable author model + self-contained Lean carrier

## The reduction

AMF-02 does not merge the whole research corpus into one market formula. Its
runtime core contains three operations only:

1. C-01 supplies a field of nearby candidate actions.
2. The Guarded Reciprocal Selector supplies admission before ranking and makes
   verification an action in its own right.
3. AMF supplies resource frugality: routine ticks preserve compute; an LLM call
   is admitted only for fresh, eventful data with budget available.

Two DL-04 properties are retained as explicit card invariants: fixed identity
and append-only trace. ITC-01 is a claim boundary, not a runtime dependency:
local imbalance does not entail a closed orbit. CI-01 supplies publication
provenance. AZ-OBS is intentionally excluded until the system receives authority
to mutate external state.

## Finite operational carrier

The public Lean file defines a hypothesis `Card`, lifecycle `Phase`, six
research `Action`s, a fixed `admissible` contract, a `goalField`, a deterministic
`choose`, and `applyAction`.

The checked surface includes:

- `choose_mem_goalField`
- `choose_is_admissible`
- `callModel_requires_gate`
- `apply_preserves_identity`
- `apply_extends_trace`
- `closed_card_cannot_reopen`
- `archive_is_absorbing`

Fresh direct check: Lean 4.32.2 PASS. No `sorry`, `admit`, or user-declared
axiom occurs in the carrier. Printed dependencies are limited to Lean's normal
logical infrastructure; no market premise is imported.

## Executable chamber

The reader mirrors the selector over support, counterevidence, noise, data
freshness, time left, attention budget, and compute budget. It exposes the
admissible action field before highlighting the selected move and appends one
record per admitted tick.

## Claim boundary

The carrier proves selector properties, not signal calibration, market
cyclicity, price direction, or profitability. Thresholds 60, 70, and 80 are
demonstration parameters. There are no trading credentials and no order
execution.

## Next point

Freeze a versioned market-card schema and a prospective replay fixture before
connecting any live exchange feed. Only then test whether the same JavaScript
and Lean decision table agree on every finite fixture row.

