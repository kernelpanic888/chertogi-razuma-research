import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import test from "node:test";

const readerUrl = new URL("../public/readers/context-that-cannot-be-erased/index.html", import.meta.url);

test("CTX-01 presents contextual mathematics as a human reading surface", async () => {
  const reader = await readFile(readerUrl, "utf8");
  assert.match(reader, /Контекст,\s*<em>который нельзя стереть<\/em>/);
  assert.match(reader, /<math display="block"/);
  assert.match(reader, /x indexed by Billing equals Free/);
  assert.match(reader, /¬<\/mo><mo>∃<\/mo>/);
  assert.match(reader, /P<\/mi><mo>\(<\/mo><mi>S<\/mi><mo>\)<\/mo><mo>=<\/mo><mi>S<\/mi>/);
  assert.match(reader, /интерференционный свидетель/);
  assert.match(reader, /классическая контекстно-индексированная система/);
  assert.doesNotMatch(reader, /<pre|<code|```|(?:^|\n)\s*theorem\s+[A-Za-z_]|:=/);
});

test("CTX-01 preserves provenance and the corpus return path", async () => {
  const reader = await readFile(readerUrl, "utf8");
  assert.match(reader, /corpus-interface\/index\.html/);
  assert.match(reader, /github\.com\/kernelpanic888\/chertogi-razuma-research\/blob\/main\/public\/readers\/context-that-cannot-be-erased\/index\.html/);
  assert.match(reader, /arxiv\.org\/abs\/1102\.0264/);
  assert.match(reader, /github\.com\/openai\/codex\/issues\/42826/);
  assert.match(reader, /MemoryGoalField\.lean/);
  assert.match(reader, /InterfacehoodClasses\.lean/);
  assert.match(reader, /MeasurementDecoherence\.lean/);
  assert.match(reader, /FIELD_OF_NEAREST_GOALS_DUAL_READER\.html/);
  assert.match(reader, /PARTIAL BRIDGE \/ OPEN EXTENSION/);
});
