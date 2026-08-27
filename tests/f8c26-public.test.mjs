import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, resolve } from "node:path";

const here = dirname(fileURLToPath(import.meta.url));
const publicHtml = readFileSync(resolve(here, "../public/index.html"), "utf8");
const routeSource = readFileSync(resolve(here, "../app/route.ts"), "utf8");

test("F8C26 finite saturation closes leastness without hiding the next boundary", () => {
  assert.match(routeSource, /first-distinction-54/);
  assert.match(publicHtml, /if-bs-f8c26-finite-saturation/);
  assert.match(publicHtml, /IsLeast\(M_a, L_tan\(a\)\)/);
  assert.match(publicHtml, /d\(p_n,q_n\)=2k_n/);
  assert.match(publicHtml, /METRIC LEASTNESS CLOSED BY F8C27/);
  assert.match(publicHtml, /data-if26-copy="ru"/);
  assert.match(publicHtml, /data-if26-copy="en"/);
  assert.doesNotMatch(publicHtml, /IntrinsicNonradialShearFiniteSaturation\.lean/);
});
