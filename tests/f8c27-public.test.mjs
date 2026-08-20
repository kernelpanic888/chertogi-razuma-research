import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, resolve } from "node:path";

const here = dirname(fileURLToPath(import.meta.url));
const publicHtml = readFileSync(resolve(here, "../public/index.html"), "utf8");
const routeSource = readFileSync(resolve(here, "../app/route.ts"), "utf8");

test("F8C27 displays simultaneous least direct and inverse metric constants", () => {
  assert.match(routeSource, /first-distinction-53/);
  assert.match(publicHtml, /if-bs-f8c27-metric-least-constants/);
  assert.match(publicHtml, /IsLeast\(F_a,K_\+\) ∧ IsLeast\(B_a,K_-\)/);
  assert.match(publicHtml, /λ_- · μ_inv = 1/);
  assert.match(publicHtml, /NOISY IDENTIFICATION CLOSED BY F8C28/);
  assert.match(publicHtml, /data-if27-copy="ru"/);
  assert.match(publicHtml, /data-if27-copy="en"/);
  assert.doesNotMatch(publicHtml, /IntrinsicNonradialShearMetricLeastConstants\.lean/);
});
