import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import test from "node:test";

const canonicalUrl = "https://chertogi-razuma-research.kernelpanic888.chatgpt.site/";

async function loadWorker() {
  const workerUrl = new URL("../dist/server/index.js", import.meta.url);
  workerUrl.searchParams.set("test", `${process.pid}-${Date.now()}-${Math.random()}`);
  return (await import(workerUrl.href)).default;
}

function environment(publicHtml) {
  return {
    ASSETS: {
      fetch: async (request) => {
        const url = new URL(request.url);
        return url.pathname === "/_canonical/page.dat"
          ? new Response(publicHtml, { status: 200, headers: { "content-type": "text/html" } })
          : new Response("Not found", { status: 404 });
      },
    },
  };
}

const context = { waitUntil() {}, passThroughOnException() {} };

test("serves one indexable canonical research map at the root", async () => {
  const [worker, publicHtml] = await Promise.all([
    loadWorker(),
    readFile(new URL("../public/index.html", import.meta.url), "utf8"),
  ]);
  const response = await worker.fetch(
    new Request("http://localhost/", { headers: { accept: "text/html" }, redirect: "manual" }),
    environment(publicHtml),
    context,
  );
  assert.equal(response.status, 200);
  assert.match(await response.text(), /Why is there something rather than nothing\?/);
  assert.equal(response.headers.get("x-robots-tag"), "index, follow, max-image-preview:large");
  assert.equal(response.headers.get("link"), `<${canonicalUrl}>; rel="canonical"`);
});

test("redirects the duplicate index path to the canonical root", async () => {
  const [worker, publicHtml] = await Promise.all([
    loadWorker(),
    readFile(new URL("../public/index.html", import.meta.url), "utf8"),
  ]);
  const response = await worker.fetch(
    new Request("http://localhost/index.html", { headers: { accept: "text/html" }, redirect: "manual" }),
    environment(publicHtml),
    context,
  );
  assert.equal(response.status, 308);
  assert.equal(response.headers.get("location"), "/");
});

test("keeps the complete corpus and its discovery metadata", async () => {
  const [publicHtml, layout, route] = await Promise.all([
    readFile(new URL("../public/index.html", import.meta.url), "utf8"),
    readFile(new URL("../app/layout.tsx", import.meta.url), "utf8"),
    readFile(new URL("../app/route.ts", import.meta.url), "utf8"),
  ]);
  assert.match(publicHtml, /<html[^>]*\blang=["']en["']/i);
  assert.match(publicHtml, /rel="canonical"/);
  assert.match(publicHtml, /application\/ld\+json/);
  assert.match(publicHtml, /if-bs-f8c31a-rational-parameter-grid/);
  assert.match(publicHtml, /EXECUTABLE PARAMETER REFINEMENT EXISTS/);
  assert.doesNotMatch(publicHtml, /Your site is taking shape|Building your site|codex-preview/);
  assert.match(layout, /metadataBase: new URL\(canonicalUrl\)/);
  assert.match(route, /rel="canonical"/);
});
