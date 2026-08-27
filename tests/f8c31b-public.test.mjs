import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

const publicHtml = await readFile(new URL("../public/index.html", import.meta.url), "utf8");
const routeSource = await readFile(new URL("../app/route.ts", import.meta.url), "utf8");

test("F8C31B closes the two-chart stereographic lift honestly", () => {
  assert.match(routeSource, /first-distinction-54/);
  assert.match(publicHtml, /if-bs-f8c31b-stereographic-diamond-lift/);
  assert.match(publicHtml, /TWO-CHART SURJECTIVITY CLOSED/);
  assert.match(publicHtml, /X\(t\).*1-t².*1\+t²/s);
  assert.match(publicHtml, /t=y\/\(1\+x\)/);
  assert.match(publicHtml, /v=s\/w/);
  assert.match(publicHtml, /QUANTITATIVE METRIC TRANSPORT: CLOSED · F8C31C/);
  assert.doesNotMatch(publicHtml, /STEREOGRAPHIC DIAMOND LIFT: OPEN/);
});
