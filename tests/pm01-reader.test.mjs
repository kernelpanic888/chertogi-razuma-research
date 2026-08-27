import assert from "node:assert/strict";
import { readFile, stat } from "node:fs/promises";
import test from "node:test";

const rootUrl = new URL("../public/index.html", import.meta.url);
const readerUrl = new URL(
  "../public/readers/poetry-of-mathematics/index.html",
  import.meta.url,
);
const wrapperUrl = new URL(
  "../public/readers/poetry-of-mathematics/hypothesis-orbit-wrapper.js",
  import.meta.url,
);
const wrapperTestUrl = new URL(
  "../public/readers/poetry-of-mathematics/hypothesis-orbit-wrapper.test.cjs",
  import.meta.url,
);
const releaseImageUrl = new URL(
  "../public/readers/poetry-of-mathematics/assets/hypothesis-orbit-geometry-release-en.png",
  import.meta.url,
);

test("PM-01 live banner is linked from the canonical public map", async () => {
  const html = await readFile(rootUrl, "utf8");
  assert.match(html, /POETRY_OF_MATHEMATICS_READER_GATE_PM_01/);
  assert.match(html, /PM-01_LIVE_HOME_BANNER/);
  assert.match(html, /href="readers\/poetry-of-mathematics\/index\.html"/);
  assert.match(html, />Hypothesis Orbit Geometry</);
  assert.match(html, />Орбитальная геометрия гипотез</);
  assert.match(html, /LEAN · PASS/);
  assert.match(html, /VAMPIRE · THEOREM/);
  assert.match(html, /E · THEOREM/);
  assert.match(html, /id="pm01-home-canvas"/);
  assert.match(
    html,
    /<script src="readers\/poetry-of-mathematics\/hypothesis-orbit-wrapper\.js"><\/script>/,
  );
});

test("PM-01 reader exposes the checked gate and its exact claim boundary", async () => {
  const html = await readFile(readerUrl, "utf8");
  assert.match(html, /<html lang="en">/);
  assert.match(html, /PM-01 · Hypothesis Orbit Geometry/);
  assert.match(html, /Орбитальная геометрия гипотез/);
  assert.match(html, /PROVENANCE_BOUNDARY_PM_01/);
  assert.match(html, /Where the Amari tradition ends here/);
  assert.match(html, /Где здесь заканчивается традиция Амари/);
  assert.match(html, /r_PM-01 = d_Fisher–Rao : OPEN/);
  assert.match(html, /NO BRIDGE THEOREM/);
  assert.match(html, /Where our epistemic model begins/);
  assert.match(html, /Где начинается наша эпистемическая модель/);
  assert.match(html, /NOT IN THE TLFL BUILD/);
  assert.match(html, /Interpretation may change angle/);
  assert.match(html, /dr &lt; 0/);
  assert.match(html, /independent-verification obligation/);
  assert.match(html, /AmariVerificationLayer/);
  assert.match(html, /not Fisher–Rao yet/);
  assert.match(html, /Vampire/);
  assert.match(html, /E ↗/);
  assert.match(html, /SZS status Theorem/);
  assert.match(html, /Spectra\/InformationGeometry/);
  assert.match(html, /8dbaaf6728d1342ae16acf79fd7eef7c59b37e63/);
  assert.match(html, /pm01-hypothesis-orbit-geometry-v0\.2\.0/);
  assert.match(html, /hypothesis-orbit-geometry-release-en\.png/);
  assert.match(html, /A checked gate is not world-validation/);
  assert.match(html, /Проверенный шлюз не валидирует мир/);
  assert.match(html, /<script src="hypothesis-orbit-wrapper\.js"><\/script>/);
  assert.match(html, /\.\.\/corpus-interface\/index\.html/);
  assert.match(html, /chertogi-razuma-research\/blob\/main\/public\/readers\/poetry-of-mathematics\/index\.html/);
  assert.doesNotMatch(html, /<link\b[^>]*\brel="stylesheet"/i);
  assert.doesNotMatch(html, /\bfetch\s*\(|\bXMLHttpRequest\b|\bWebSocket\s*\(/);
});

test("PM-01 wrapper, finite checks, and release image are published beside the reader", async () => {
  const [wrapper, checks, image] = await Promise.all([
    readFile(wrapperUrl, "utf8"),
    readFile(wrapperTestUrl, "utf8"),
    stat(releaseImageUrl),
  ]);
  assert.match(wrapper, /function rotateBy/);
  assert.match(wrapper, /function tryRadialMove/);
  assert.match(wrapper, /function tryPromotion/);
  assert.match(wrapper, /not generated\s+\* from Lean/);
  assert.doesNotMatch(wrapper, /\bfetch\s*\(|\bXMLHttpRequest\b|\bWebSocket\s*\(/);
  assert.match(checks, /PM-01 browser wrapper: 10 checks PASS/);
  assert.ok(image.size > 1_000_000);
});
