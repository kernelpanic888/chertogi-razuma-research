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

test("orders all homepage reader banners by their latest update", async () => {
  const home = await readFile(new URL("../public/index.html", import.meta.url), "utf8");
  const banners = [...home.matchAll(
    /<aside class="(?:research-lab-gate|pm01-home)[^"]*" data-reader-updated="(\d{4}-\d{2}-\d{2})"[\s\S]*?<\/aside>/g,
  )].map((match, sourceIndex) => ({
    html: match[0],
    sourceIndex,
    updated: match[1],
  }));

  assert.equal(banners.length, 9);
  for (const banner of banners) {
    const visibleDateCount = banner.html.match(new RegExp(`datetime="${banner.updated}"`, "g"))?.length ?? 0;
    assert.equal(visibleDateCount, 2, `RU and EN update dates must match ${banner.updated}`);
  }

  const sortedDates = banners
    .sort((a, b) => b.updated.localeCompare(a.updated) || a.sourceIndex - b.sourceIndex)
    .map((banner) => banner.updated);
  assert.deepEqual(sortedDates, [
    "2026-08-29",
    "2026-08-28",
    "2026-08-28",
    "2026-08-25",
    "2026-08-23",
    "2026-08-20",
    "2026-08-20",
    "2026-08-20",
    "2026-08-20",
  ]);
  assert.match(home, /shelf\.dataset\.sorted="latest-updated-first"/);
});

test("publishes ITC-01 as a canonical but individually voiced interactive chamber", async () => {
  const [home, reader, registry, publications] = await Promise.all([
    readFile(new URL("../public/index.html", import.meta.url), "utf8"),
    readFile(new URL("../public/readers/invariant-transport-closure/index.html", import.meta.url), "utf8"),
    readFile(new URL("../public/corpus/interfaces.json", import.meta.url), "utf8"),
    readFile(new URL("../public/publications/records.json", import.meta.url), "utf8"),
  ]);
  assert.match(home, /distinction → transition → trace → return/);
  assert.match(home, /data-voice="transport"/);
  assert.match(home, /readers\/invariant-transport-closure\/index\.html/);
  assert.match(reader, /τγ\(I\(C₀\)\) = I\(C₀\)/);
  assert.match(reader, /return of a chosen invariant ⇒ τγ = id/);
  assert.match(reader, /corpus-interface\/index\.html/);
  const corpusRecord = JSON.parse(registry).readers.find((item) => item.id === "ITC-01");
  const publicationRecord = JSON.parse(publications).records.find((item) => item.id === "ITC-01-RC");
  assert.equal(corpusRecord.status, "linked");
  assert.match(corpusRecord.formalUrls[0], /blob\/74a2a806a229830c668e66be233de2fda7bfc944\//);
  assert.equal(publicationRecord.status, "release-candidate");
  assert.equal(publicationRecord.doi, null);
  assert.equal(publicationRecord.releaseTag, null);
});
