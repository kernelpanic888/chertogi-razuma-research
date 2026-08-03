import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, resolve } from "node:path";

const here = dirname(fileURLToPath(import.meta.url));
const publicHtml = readFileSync(resolve(here, "../public/index.html"), "utf8");
const routeSource = readFileSync(resolve(here, "../app/page.tsx"), "utf8");

test("F8C28 exposes a certified noisy interval and hands raw transport to F8C29", () => {
  assert.match(routeSource, /first-distinction-53/);
  assert.match(publicHtml, /if-bs-f8c28-noisy-identifiability/);
  assert.match(publicHtml, /A_noisy ⊆ \[a_low,a_high\]/);
  assert.match(publicHtml, /ε_F=ε_B=0 ⇒ UNIQUE a/);
  assert.match(publicHtml, /RAW SAMPLE TRANSPORT CLOSED BY F8C29/);
  assert.match(publicHtml, /data-if28-copy="ru"/);
  assert.match(publicHtml, /data-if28-copy="en"/);
  assert.doesNotMatch(publicHtml, /IntrinsicNonradialShearNoisyIdentifiability\.lean/);
});
