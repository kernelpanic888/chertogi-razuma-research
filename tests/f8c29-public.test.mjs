import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, resolve } from "node:path";

const here = dirname(fileURLToPath(import.meta.url));
const publicHtml = readFileSync(resolve(here, "../public/index.html"), "utf8");
const routeSource = readFileSync(resolve(here, "../app/route.ts"), "utf8");

test("F8C29 transports raw finite samples into certified F8C28 budgets", () => {
  assert.match(routeSource, /first-distinction-54/);
  assert.match(publicHtml, /if-bs-f8c29-raw-budget-transport/);
  assert.match(publicHtml, /S⁻ ≤ S_exact ≤ S⁺/);
  assert.match(publicHtml, /O=√S⁺ · ε=√S⁺−√S⁻/);
  assert.match(publicHtml, /RAW SAMPLE ⇒ CERTIFIED NOISY READING/);
  assert.match(publicHtml, /EXECUTABLE δ-NET CLOSED BY F8C30/);
  assert.match(publicHtml, /data-if29-copy="ru"/);
  assert.match(publicHtml, /data-if29-copy="en"/);
  assert.doesNotMatch(publicHtml, /IntrinsicNonradialShearRawSampleCertification\.lean/);
});
