import fs from "node:fs";
import path from "node:path";
import test from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";

import {
  inspectPublicStaticBoundary,
} from "../scripts/check-public-static-boundary.mjs";

const testDir = path.dirname(fileURLToPath(import.meta.url));
const projectRoot = path.resolve(testDir, "..");
const publicHtml = fs.readFileSync(path.join(projectRoot, "public/index.html"), "utf8");
const publicHosting = JSON.parse(
  fs.readFileSync(path.join(projectRoot, ".openai/hosting.json"), "utf8"),
);

function failingIds(html = publicHtml, hosting = publicHosting) {
  return inspectPublicStaticBoundary({ html, hosting }).checks
    .filter((check) => !check.pass)
    .map((check) => check.id);
}

test("current public bundle satisfies the P0 boundary", () => {
  const result = inspectPublicStaticBoundary({
    html: publicHtml,
    hosting: publicHosting,
  });
  assert.equal(result.ok, true);
});

test("fetch collector injection is rejected", () => {
  assert.ok(failingIds(`${publicHtml}<script>fetch('/collect')</script>`)
    .includes("network-fetch"));
});

test("external script injection is rejected", () => {
  assert.ok(failingIds(`${publicHtml}<script src="https://example.test/x.js"></script>`)
    .includes("scripts-inline-only"));
});

test("remote stylesheet injection is rejected", () => {
  assert.ok(failingIds(`${publicHtml}<link rel="stylesheet" href="https://example.test/x.css">`)
    .includes("styles-inline-only"));
});

test("cookie capability injection is rejected", () => {
  assert.ok(failingIds(`${publicHtml}<script>document.cookie = 'x=1'</script>`)
    .includes("no-cookie-api"));
});

test("beacon capability injection is rejected", () => {
  assert.ok(failingIds(`${publicHtml}<script>navigator.sendBeacon('/x', '1')</script>`)
    .includes("network-beacon"));
});

test("websocket capability injection is rejected", () => {
  assert.ok(failingIds(`${publicHtml}<script>new WebSocket('wss://example.test')</script>`)
    .includes("network-websocket"));
});

test("dynamic provider-style script injection is rejected", () => {
  const injected = `${publicHtml}<script>
    const challenge = document.createElement('script');
    challenge.src = '/cdn-cgi/challenge-platform/example.js';
  </script>`;
  const failures = failingIds(injected);
  assert.ok(failures.includes("dynamic-script-create"));
  assert.ok(failures.includes("dynamic-source-assignment"));
});

test("dynamic source attribute injection is rejected", () => {
  const injected = `${publicHtml}<script>
    const challenge = document.createElement('script');
    challenge.setAttribute('src', '/provider/example.js');
  </script>`;
  const failures = failingIds(injected);
  assert.ok(failures.includes("dynamic-script-create"));
  assert.ok(failures.includes("dynamic-source-attribute"));
});

test("form and public admin route injection are rejected", () => {
  const failures = failingIds(`${publicHtml}<form action="/admin"></form>`);
  assert.ok(failures.includes("html-form"));
  assert.ok(failures.includes("no-admin-navigation"));
});

test("iframe capability injection is rejected", () => {
  assert.ok(failingIds(`${publicHtml}<iframe src="https://example.test"></iframe>`)
    .includes("html-iframe"));
});

test("unregistered browser-storage key is rejected", () => {
  assert.ok(failingIds(`${publicHtml}<script>localStorage.setItem(SECRET_KEY, 'x')</script>`)
    .includes("registered-local-storage-only"));
});

test("only the anonymous DB counter binding is permitted in P0", () => {
  assert.equal(failingIds(publicHtml, {
    ...publicHosting,
    d1: "DB",
  }).includes("d1-counter-only"), false);
  assert.ok(failingIds(publicHtml, {
    ...publicHosting,
    d1: "PRIVATE_DATA",
  }).includes("d1-counter-only"));
});

test("R2 binding promotes the project out of P0 and is rejected", () => {
  assert.ok(failingIds(publicHtml, {
    ...publicHosting,
    r2: { binding: "FILES" },
  }).includes("r2-unbound"));
});
