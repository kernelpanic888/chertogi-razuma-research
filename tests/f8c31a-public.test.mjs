import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, resolve } from "node:path";

const here = dirname(fileURLToPath(import.meta.url));
const publicHtml = readFileSync(resolve(here, "../public/index.html"), "utf8");
const routeSource = readFileSync(resolve(here, "../app/route.ts"), "utf8");

test("F8C31A supplies an executable convergent rational parameter grid", () => {
  assert.match(routeSource, /first-distinction-54/);
  assert.match(publicHtml, /if-bs-f8c31a-rational-parameter-grid/);
  assert.match(publicHtml, /qₖ=−1\+2k\/\(n\+1\)/);
  assert.match(publicHtml, /k=floor\(\(x\+1\)\(n\+1\)\/2\)/);
  assert.match(publicHtml, /δₙ=2\/\(n\+1\) → 0/);
  assert.match(publicHtml, /EXECUTABLE PARAMETER REFINEMENT EXISTS/);
  assert.match(publicHtml, /STEREOGRAPHIC LIFT CLOSED BY F8C31B/);
  assert.match(publicHtml, /data-if31-copy="ru"/);
  assert.match(publicHtml, /data-if31-copy="en"/);
  assert.doesNotMatch(publicHtml, /IntrinsicNonradialShearRationalParameterRefinement\.lean/);
});
