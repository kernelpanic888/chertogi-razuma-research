import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import test from "node:test";

const reader = await readFile(
  new URL("../public/readers/adaptive-market-frugality/index.html", import.meta.url),
  "utf8",
);
const lean = await readFile(
  new URL(
    "../public/readers/adaptive-market-frugality/AdaptiveMarketHypothesisSteward.lean",
    import.meta.url,
  ),
  "utf8",
);

test("AMF-02 keeps one minimal operational core", () => {
  for (const required of [
    "Gᵣ(Cₜ)",
    "Q*(Cₜ,Hₜ,g)",
    "callModel ⇒ fresh ∧ eventful ∧ compute&gt;0",
    "Traceₜ ⪯ Traceₜ₊₁",
    "localImbalance ⇏ ClosedOrbit",
    "selection ≠ external authority",
  ]) {
    assert.match(reader, new RegExp(required.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")));
  }
});

test("AMF-02 exposes exact corpus roles without importing Agent Zero", () => {
  assert.match(reader, /connectedness-c01\/FIELD_OF_NEAREST_GOALS_DUAL_READER\.html/);
  assert.match(reader, /guarded-reciprocal-selector\/GUARDED_RECIPROCAL_SELECTOR_DUAL_READER\.html/);
  assert.match(reader, /digital-life-living-model/);
  assert.match(reader, /invariant-transport-closure/);
  assert.match(reader, /NOT IN CORE \/ AZ-OBS/);
  assert.match(reader, /У AMF-02 нет торговых ключей/);
});

test("AMF-02 Lean carrier states the advertised theorems and has no gaps", () => {
  for (const theorem of [
    "choose_mem_goalField",
    "choose_is_admissible",
    "callModel_requires_gate",
    "apply_preserves_identity",
    "apply_extends_trace",
    "closed_card_cannot_reopen",
    "archive_is_absorbing",
  ]) {
    assert.match(lean, new RegExp(`theorem ${theorem}`));
    assert.match(reader, new RegExp(theorem));
  }
  assert.doesNotMatch(lean, /\bsorry\b|\badmit\b|\baxiom\b/);
});

test("AMF-01 remains a separately named legacy surface", () => {
  assert.match(reader, /AMF-01 \/ BUFFER/);
  assert.match(reader, /AdaptiveMarketFrugality\.lean/);
  assert.match(reader, /AMF‑01 не переписан/);
});
