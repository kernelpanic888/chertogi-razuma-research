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

## D-EXP-01 / Second-observer experiment

Denys's applied request is separated from the mathematical core and stated as
a measurable experiment. Its hypothesis is that an additional machine layer
can reduce analyst fatigue, review time, and accidental decision reversals
without claiming to predict the future.

Two modes are compared:

1. `CARD ONLY` is the inexpensive baseline over a frozen card with source,
   snapshot time, thesis, confirmation, invalidation, and feature version.
2. `CARD + EXCHANGE` enriches the card on events with candles, volume, and only
   the additional fields on which the thesis actually depends. The LLM is not
   called on every candle.

The verdict must be `SUPPORTS`, `WEAKENS`, or `INDETERMINATE`. The last value is
admissible only with explicit missing data and a nearest review. `strengthScore`
is an experimental scale, not a calibrated probability.

The reader adds an editable cost calculator, asynchronous append-only trace,
Grafana projection fields, and a `HUMAN` versus `HUMAN+MODEL` comparison over
the same cards with hidden outcomes. Primary metrics are review time, fatigue,
unsupported decision reversals, missed evidence, model-call count, and cost per
hour freed.

### Two fields, two semantics

The original AMF-01 `STATE FIELD` interaction is restored with K, K*, δ band,
BELOW/NEAR/ABOVE zones, and the original resource-policy selector. It remains
an AMF-01 legacy surface and denotes neither price nor probability.

D-EXP-01 receives a visual twin called `EVENT FIELD`: Eₜ is compared with
θcall inside an editable band. This projection shows only whether the event
gate opens. Even ABOVE does not remove freshness, conflict-verification, and
available-compute requirements.

## Claim boundary

The carrier proves selector properties, not signal calibration, market
cyclicity, price direction, or profitability. Thresholds 60, 70, and 80 are
demonstration parameters. There are no trading credentials and no order
execution.

## Next point

Freeze a versioned JSON schema for card and verdict, then build the first blind
replay set without a live exchange feed. Only after the `CARD ONLY` baseline
should event-driven `CARD + EXCHANGE` enrichment be added and its incremental
value compared with its incremental cost.
