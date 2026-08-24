import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import test from "node:test";

const rootUrl = new URL("../public/index.html", import.meta.url);
const readerUrl = new URL(
  "../public/readers/poetry-of-mathematics/index.html",
  import.meta.url,
);

test("PM-01 is linked from the canonical public map", async () => {
  const html = await readFile(rootUrl, "utf8");
  assert.match(html, /POETRY_OF_MATHEMATICS_READER_GATE_PM_01/);
  assert.match(html, /href="readers\/poetry-of-mathematics\/index\.html"/);
  assert.match(html, />Поэзия математики</);
  assert.match(html, />Poetry of Mathematics</);
});

test("PM-01 is bilingual, self-contained, and preserves its red boundary", async () => {
  const html = await readFile(readerUrl, "utf8");
  assert.match(html, /lang="ru"/);
  assert.match(html, /Салкуцан Алексей Анатольевич/);
  assert.match(html, /Author of the research frame/);
  assert.match(html, /STANDARD OPTICS/);
  assert.match(html, /DEFINED HERE/);
  assert.match(html, /AUTHOR CANON/);
  assert.match(html, /RED BOUNDARY/);
  assert.match(html, /E = ℝ³/);
  assert.match(html, /p ∈ Sh ⇔/);
  assert.match(html, /σ\(p\) := 1 −/);
  assert.match(html, /∂<sub>Π<\/sub>Sh ⊆/);
  assert.match(html, /CANONICAL FORMAL SOURCE/);
  assert.match(html, /TMI-Lean-Formal-Library\/tree\/main\/research\/poetry-of-mathematics-v0\.1/);
  assert.match(html, /Мы не доказываем иные миры/);
  assert.match(html, /We do not prove other worlds/);
  assert.match(html, /V-02 \/ Магия формулы/);
  assert.match(html, /И здесь рождается магия/);
  assert.match(html, /Magic here is not supernatural/);
  assert.match(html, /NOT A MIRACLE CLAIM/);
  assert.match(html, /MODEL \/ MAGIC ≠ POETRY/);
  assert.match(html, /Магия не поэзия/);
  assert.match(html, /поэзия — чтение магии/);
  assert.match(html, /Почему мир не магичен/);
  assert.match(html, /Магичен\. И потому поэтичен/);
  assert.match(html, /V-03 \/ Красота и проверка/);
  assert.match(html, /BEAUTY ≠ PROOF/);
  assert.match(html, /Красота сама по себе не доказательство/);
  assert.match(html, /BeautyCandidate/);
  assert.match(html, /RealityTraceCandidate/);
  const leanSkeleton = html.match(/universe u[\s\S]*?exact hChecked/)?.[0] ?? "";
  assert.ok(leanSkeleton);
  assert.doesNotMatch(leanSkeleton, /\d/);
  assert.match(html, /href="\.\.\/\.\.\/"/);
  assert.match(html, /HOME ↖/);
  assert.match(html, /вычислимое присутствие ограничения на поверхности мира/);
  assert.match(html, /computable presence of a constraint on the surface of the world/);
  assert.match(html, /const LANGUAGE_KEY = 'pm-language'/);
  assert.match(html, /container-type:inline-size/);
  assert.match(html, /h1>.en em\{font-size:min\(\.72em,10\.5cqw\)\}/);
  assert.doesNotMatch(html, /<script\b[^>]*\bsrc=/i);
  assert.doesNotMatch(html, /<link\b[^>]*\brel="stylesheet"/i);
  assert.doesNotMatch(html, /\bfetch\s*\(|\bXMLHttpRequest\b|\bWebSocket\s*\(/);
});
