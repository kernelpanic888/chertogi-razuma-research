import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import test from "node:test";

const reader = await readFile(
  new URL("../public/readers/adaptive-market-frugality/index.html", import.meta.url),
  "utf8",
);
const legacyReader = await readFile(
  new URL(
    "../public/readers/adaptive-market-frugality-amf01/index.html",
    import.meta.url,
  ),
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

test("AMF-01 remains separately named and preserved in full", () => {
  assert.match(reader, /AMF-01 \/ BUFFER/);
  assert.match(reader, /AdaptiveMarketFrugality\.lean/);
  assert.match(reader, /AMF‑01 сохранён целиком/);
  assert.match(reader, /adaptive-market-frugality-amf01\//);
});

test("D-EXP-01 states Denys's second-observer experiment explicitly", () => {
  for (const required of [
    "Эксперимент второго наблюдателя",
    "D-EXP-01 / RESEARCH QUESTION",
    "MODE A / BASELINE",
    "MODE B / ENRICHED",
    "CARD + EXCHANGE",
    "verdict ∈ {SUPPORTS, WEAKENS, INDETERMINATE}",
    "INDETERMINATE ⇒ missingData ≠ ∅ ∧ nextReview ≠ ∅",
    "GRAFANA = PROJECTION, NOT SOURCE.",
    "HUMAN vs HUMAN+MODEL",
  ]) {
    assert.ok(reader.includes(required), `missing experiment contract: ${required}`);
  }
});

test("D-EXP-01 exposes an editable event-budget calculator", () => {
  for (const id of [
    "cost-calls",
    "cost-days",
    "cost-input",
    "cost-output",
    "cost-in-rate",
    "cost-out-rate",
    "cost-data",
    "cost-total",
  ]) {
    assert.match(reader, new RegExp(`id="${id}"`));
  }
  assert.match(reader, /experimentMode==='exchange'/);
  assert.match(reader, /dataMode, strengthScore, counterevidence, verdict, phase, modelCalls/);
});

test("AMF-01 original K/K* state field is restored as an interactive legacy surface", () => {
  for (const required of [
    "STATE FIELD / ПОЛЕ СОСТОЯНИЙ · AMF-01 ORIGINAL",
    "id=\"buffer-band\"",
    "id=\"buffer-target-pin\"",
    "id=\"buffer-resource-pin\"",
    "data-label=\"K*\"",
    "data-label=\"K\"",
    "BELOW / НИЖЕ",
    "NEAR / РЯДОМ",
    "ABOVE / ВЫШЕ",
    "const chooseBuffer=",
    "K(t+1) = ",
  ]) {
    assert.ok(reader.includes(required), `missing restored AMF-01 field: ${required}`);
  }
});

test("D-EXP-01 event field is a separate Eₜ/θcall projection", () => {
  for (const required of [
    "EVENT FIELD / ПОЛЕ СОБЫТИЯ · D-EXP-01",
    "data-label=\"θcall\"",
    "data-label=\"Eₜ\"",
    "BELOW / TICK",
    "NEAR / VERIFY",
    "ABOVE / EVENT",
    "id=\"event-intensity\"",
    "id=\"event-threshold\"",
    "id=\"event-bandwidth\"",
    "ABOVE opens the event gate only",
  ]) {
    assert.ok(reader.includes(required), `missing D-EXP-01 event field: ${required}`);
  }
  assert.match(reader, /callModel.*freshness.*compute/);
});

test("AMF-01 is preserved as its exact standalone live selector chamber", () => {
  assert.match(reader, /href="\.\.\/adaptive-market-frugality-amf01\//);
  for (const required of [
    "AMF-01 / MARKET SELECTOR",
    "Live selector chamber",
    "STATE FIELD / ПОЛЕ СОСТОЯНИЙ",
    "State controls",
    "data-action=\"accumulate\"",
    "data-action=\"hold\"",
    "data-action=\"investAdaptation\"",
    "data-action=\"reduceRisk\"",
    "data-action=\"spendQuality\"",
    "id=\"metric-k\"",
    "id=\"metric-target\"",
    "id=\"metric-band\"",
    "id=\"metric-next\"",
  ]) {
    assert.ok(legacyReader.includes(required), `missing standalone AMF-01 surface: ${required}`);
  }
  assert.match(
    legacyReader,
    /rel="canonical" href="https:\/\/chertogi-razuma-research\.kernelpanic888\.chatgpt\.site\/readers\/adaptive-market-frugality-amf01\//,
  );
});
