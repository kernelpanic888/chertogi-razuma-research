import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, resolve } from "node:path";

const here = dirname(fileURLToPath(import.meta.url));
const publicHtml = readFileSync(resolve(here, "../public/index.html"), "utf8");
const routeSource = readFileSync(resolve(here, "../app/page.tsx"), "utf8");

test("F8C30 supplies an executable rational coarse net", () => {
  assert.match(routeSource, /first-distinction-53/);
  assert.match(publicHtml, /if-bs-f8c30-executable-coarse-net/);
  assert.match(publicHtml, /c₀=\(\(1,0\),0\)/);
  assert.match(publicHtml, /D ⊆ B\(c₀,2\)/);
  assert.match(publicHtml, /G₀=\{c₀\} · δ₀=2/);
  assert.match(publicHtml, /EXECUTABLE REFERENCE CERTIFICATE EXISTS/);
  assert.match(publicHtml, /PARAMETER REFINEMENT CLOSED BY F8C31A/);
  assert.match(publicHtml, /data-if30-copy="ru"/);
  assert.match(publicHtml, /data-if30-copy="en"/);
  assert.doesNotMatch(publicHtml, /IntrinsicNonradialShearExecutableCoarseNet\.lean/);
});
