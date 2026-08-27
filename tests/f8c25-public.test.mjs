import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

const root = new URL("../", import.meta.url);
const publicHtml = readFileSync(new URL("public/index.html", root), "utf8");
const routeSource = readFileSync(new URL("app/route.ts", root), "utf8");

test("F8C25 actual-pair transport is present and honestly bounded", () => {
  assert.match(routeSource, /first-distinction-54/);
  assert.match(publicHtml, /if-bs-f8c25-actual-pair-transport/);
  assert.match(publicHtml, /ACTUAL-PAIR TRANSPORT/);
  assert.match(publicHtml, /exists_centered_record_of_unit_pair/);
  assert.match(publicHtml, /forwardBlowUpSq_actual_pair_exact_bound/);
  assert.match(publicHtml, /m·h=0/);
  assert.match(publicHtml, /r²\+k²=1/);
  assert.match(publicHtml, /\|Φ_a\(p\)-Φ_a\(q\)\| ≤ L_tan\(a\) d\(p,q\)/);
  assert.match(publicHtml, /LEASTNESS CLOSED BY F8C26/);
  assert.doesNotMatch(publicHtml, /ACTUAL-PAIR TRANSPORT: OPEN/);
});
