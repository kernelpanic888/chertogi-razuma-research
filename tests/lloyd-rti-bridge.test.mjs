import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import test from "node:test";

const readerUrl = new URL(
  "../public/readers/activation-relic-shadow-boundary/index.html",
  import.meta.url,
);

test("publishes the Lloyd to RTI bridge with explicit provenance", async () => {
  const reader = await readFile(readerUrl, "utf8");

  assert.match(reader, /id="lloyd-bridge"/);
  assert.match(reader, /01 \/ UPSTREAM · LLOYD/);
  assert.match(reader, /03 \/ OUR LIFT · TMI \+ RTI/);
  assert.match(reader, /not a verbatim Lloyd equation/);
  assert.match(reader, /Their compatibility is a new bridge, not a Lloyd result/);
  assert.match(reader, /Вселенная вычисляет себя/);
  assert.match(reader, /Вселенная может вычислять себя лишь через интерфейсы/);
  assert.match(reader, /OUR HYPOTHESIS · NOT A LLOYD RESULT/);
});

test("keeps Lloyd's P-CTC map exact and nonzero-weight guarded", async () => {
  const reader = await readFile(readerUrl, "utf8");

  assert.match(reader, /C<sub>U<\/sub> := Tr<sub>CTC<\/sub>\[U\]/);
  assert.match(reader, /𝒩<sub>U<\/sub>\[ρ\] := C<sub>U<\/sub>ρC<sub>U<\/sub><sup>†<\/sup> \/ Tr\[C<sub>U<\/sub>ρC<sub>U<\/sub><sup>†<\/sup>\]/);
  assert.match(reader, /w<sub>U<\/sub>\(ρ\) := Tr\[C<sub>U<\/sub>ρC<sub>U<\/sub><sup>†<\/sup>\] &gt; 0/);
  assert.match(reader, /https:\/\/doi\.org\/10\.1103\/PhysRevD\.84\.025007/);
  assert.match(reader, /https:\/\/doi\.org\/10\.1103\/PhysRevLett\.106\.040403/);
});

test("states the interface lift and its no-smuggling boundary", async () => {
  const reader = await readFile(readerUrl, "utf8");

  assert.match(reader, /Read<sub>p<\/sub> ∘ 𝒥<sub>p←q<\/sub> = Θ<sub>p←q<\/sub> ∘ Read<sub>q<\/sub>/);
  assert.match(reader, /QRR\(p,q,ρ,𝒥\) :⇔/);
  assert.match(reader, /Neither the P-CTC formula alone nor 1&lt;1000 proves this/);
  assert.match(reader, /Lloyd does not prove TMI/);
  assert.match(reader, /https:\/\/arxiv\.org\/abs\/1312\.4455/);
  assert.match(reader, /https:\/\/arxiv\.org\/abs\/1307\.0378/);
});
