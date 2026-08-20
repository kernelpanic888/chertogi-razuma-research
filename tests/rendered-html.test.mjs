import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import test from "node:test";

async function renderPath(pathname = "/") {
  const workerUrl = new URL("../dist/server/index.js", import.meta.url);
  workerUrl.searchParams.set("test", `${process.pid}-${Date.now()}`);
  const { default: worker } = await import(workerUrl.href);
  const publicHtml = await readFile(new URL("../public/index.html", import.meta.url), "utf8");

  return worker.fetch(
    new Request(`http://localhost${pathname}`, {
      headers: { accept: "text/html" },
      redirect: "manual",
    }),
    {
      ASSETS: {
        fetch: async (request) => new URL(request.url).pathname === "/_canonical/page.dat"
          ? new Response(publicHtml, { headers: { "Content-Type": "text/html; charset=utf-8" } })
          : new Response("Not found", { status: 404 }),
      },
    },
    {
      waitUntil() {},
      passThroughOnException() {},
    },
  );
}

test("serves one indexable canonical research map at the root", async () => {
  const response = await renderPath();
  assert.equal(response.status, 200);
  assert.match(response.headers.get("content-type") ?? "", /^text\/html/);
  assert.equal(response.headers.get("x-robots-tag"), "index, follow, max-image-preview:large");
  assert.match(response.headers.get("link") ?? "", /rel="canonical"/);
});

test("redirects the duplicate index path to the canonical root", async () => {
  const response = await renderPath("/index.html?v=legacy");
  assert.equal(response.status, 308);
  assert.equal(response.headers.get("location"), "http://localhost/");
});

test("ships F8C10 without the disposable starter preview", async () => {
  const [publicHtml, page, layout] = await Promise.all([
    readFile(new URL("../public/index.html", import.meta.url), "utf8"),
    readFile(new URL("../app/page.tsx", import.meta.url), "utf8"),
    readFile(new URL("../app/layout.tsx", import.meta.url), "utf8"),
  ]);

  assert.match(publicHtml, /<html[^>]*\blang=["']en["']/i);
  assert.match(publicHtml, /if-bs-f8c10-compact-reduction/);
  assert.match(publicHtml, /COMPACT CHORD REDUCTION/);
  assert.match(publicHtml, /C≤max\(1,Cfar,Ccore\)/);
  assert.match(publicHtml, /RED BOUNDARY/);
  assert.match(publicHtml, /if-bs-f8c11-closed-core/);
  assert.match(publicHtml, /if-bs-f8c12-diagonal-blowup/);
  assert.match(publicHtml, /DIRECTIONAL BLOW-UP/);
  assert.match(publicHtml, /forwardBlowUpSqRegularity/);
  assert.match(publicHtml, /if-bs-f8c13-inverse-blowup/);
  assert.match(publicHtml, /INVERSE BLOW-UP/);
  assert.match(publicHtml, /inverseCertificateGap/);
  assert.match(publicHtml, /if-bs-f8c14-realizable-blowup/);
  assert.match(publicHtml, /REALIZABLE BLOW-UP/);
  assert.match(publicHtml, /directionalDiamondBand/);
  assert.match(publicHtml, /if-bs-f8c15-realizable-closure/);
  assert.match(publicHtml, /EXACT REALIZABLE CLOSURE/);
  assert.match(publicHtml, /realizableClosureEq/);
  assert.match(publicHtml, /if-bs-f8c16-exact-certificates/);
  assert.match(publicHtml, /EXACT-DOMAIN CERTIFICATES/);
  assert.match(publicHtml, /certifiedDiamondInverseMeshTerm/);
  assert.match(publicHtml, /CLOSED CORE \+ FINITE δ-NET/);
  assert.match(publicHtml, /f≤Mnoise\+Lδ/);
  assert.match(publicHtml, /if-bs-f8c17-sharp-envelope/);
  assert.match(publicHtml, /SHARP SPECTRAL ENVELOPE/);
  assert.match(publicHtml, /exactDiamond_envelope_isSharp/);
  assert.match(publicHtml, /sharpDiamondInverseCertificateGap/);
  assert.match(publicHtml, /min_D Φₐ=λ₋/);
  assert.match(publicHtml, /if-bs-f8c18-slope-envelope/);
  assert.match(publicHtml, /EXACT SLOPE ENVELOPE/);
  assert.match(publicHtml, /exactSlopeRadius_isSharp/);
  assert.match(publicHtml, /slopeEnvelopeInverseCertificateGap/);
  assert.match(publicHtml, /R\(a\)=√\(a²\+\(1\+a\)²\)/);
  assert.match(publicHtml, /if-bs-f8c19-circle-coupling/);
  assert.match(publicHtml, /CIRCLE COUPLING/);
  assert.match(publicHtml, /circle_xSquare_strict/);
  assert.match(publicHtml, /circleCoupledInverseCertificateGap/);
  assert.match(publicHtml, /Lcircle=1\+2\(1\+a\)R\(a\)/);
  assert.match(publicHtml, /if-bs-f8c20-asymptotic-witness/);
  assert.match(publicHtml, /ASYMPTOTIC CIRCLE WITNESS/);
  assert.match(publicHtml, /circle_xSquare_coefficient_one_isLeast/);
  assert.match(publicHtml, /circleLift_forward_cancellation/);
  assert.match(publicHtml, /ΔΦₐ=-4at\/\(1\+t²\)/);
  assert.match(publicHtml, /if-bs-f8c21-tangent-envelope/);
  assert.match(publicHtml, /if-bs-f8c22-stationary-envelope/);
  assert.match(publicHtml, /UNIQUE STATIONARY ENVELOPE/);
  assert.match(publicHtml, /existsUnique_slopeStationaryRoot/);
  assert.match(publicHtml, /halfAmplitude_exactLocalTangentModulus/);
  assert.match(publicHtml, /3t⁴ \+ 22t³ − 2t² − 10t − 5 = 0/);
  assert.match(publicHtml, /EXACT TANGENT ENVELOPE/);
  assert.match(publicHtml, /tangentForwardRaw_eq_differential/);
  assert.match(publicHtml, /exactLocalTangentModulus_isGreatest/);
  assert.match(publicHtml, /Ltan=2aE\(a\)/);
  assert.doesNotMatch(publicHtml, /Your site is taking shape|Building your site/);
  assert.doesNotMatch(publicHtml, /codex-preview|react-loading-skeleton/);

  assert.match(publicHtml, /if-bs-f8c29-raw-budget-transport/);
  assert.match(publicHtml, /RAW SAMPLE ⇒ CERTIFIED NOISY READING/);
  assert.match(publicHtml, /if-bs-f8c30-executable-coarse-net/);
  assert.match(publicHtml, /EXECUTABLE REFERENCE CERTIFICATE EXISTS/);
  assert.match(publicHtml, /if-bs-f8c31a-rational-parameter-grid/);
  assert.match(publicHtml, /EXECUTABLE PARAMETER REFINEMENT EXISTS/);
  assert.match(page, /redirect\("\/index\.html"\)/);
  assert.doesNotMatch(page, /_sites-preview|SkeletonPreview|codex-preview/);
  assert.match(layout, /export const metadata:\s*Metadata/);
  assert.match(layout, /<html lang="en">/);
  assert.doesNotMatch(layout, /_sites-preview|SkeletonPreview|codex-preview/);
});
