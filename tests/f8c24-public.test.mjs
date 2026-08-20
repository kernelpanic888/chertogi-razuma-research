import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

const root = new URL("../", import.meta.url);
const publicHtml = readFileSync(new URL("public/index.html", root), "utf8");
const routeSource = readFileSync(new URL("app/route.ts", root), "utf8");

test("F8C24 exact centered envelope is present in the public source", () => {
  assert.match(routeSource, /public\/index\.html\?raw/);
  assert.match(routeSource, /chertogi-razuma-research\.kernelpanic888\.chatgpt\.site/);
  assert.match(publicHtml, /if-bs-f8c24-centered-envelope/);
  assert.match(publicHtml, /CENTERED TWO-POINT ENVELOPE/);
  assert.match(publicHtml, /centeredTwoPointEnvelope_le_exact/);
  assert.match(publicHtml, /exactTangentEnvelope_isGreatest_centered/);
  assert.match(publicHtml, /C_a\(X,Y,r,k\)/);
  assert.match(publicHtml, /TRANSPORT CLOSED BY F8C25/);
});
