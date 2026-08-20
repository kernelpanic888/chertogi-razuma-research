import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

const root = new URL("../", import.meta.url);
const publicHtml = readFileSync(new URL("public/index.html", root), "utf8");
const routeSource = readFileSync(new URL("app/route.ts", root), "utf8");

test("F8C23 finite-chord bridge is present in the public source", () => {
  assert.match(routeSource, /public\/index\.html\?raw/);
  assert.match(routeSource, /chertogi-razuma-research\.kernelpanic888\.chatgpt\.site/);
  assert.match(publicHtml, /if-bs-f8c23-chord-bridge/);
  assert.match(publicHtml, /FINITE CHORD BRIDGE/);
  assert.match(publicHtml, /forwardBlowUpSq_chord_bridge/);
  assert.match(publicHtml, /exactLocalTangentModulus_le_chordBridgeModulus/);
  assert.match(publicHtml, /G\(a\).*2a/);
  assert.match(publicHtml, /LEAST GLOBAL MODULUS: OPEN/);
});
