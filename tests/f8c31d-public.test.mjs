import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

const htmlPath = new URL('../public/index.html', import.meta.url);

test('F8C31D materializes rational records into the existing certificate chain', async () => {
  const html = await readFile(htmlPath, 'utf8');
  assert.match(html, /if-bs-f8c31d-rational-measurement-table/);
  assert.match(html, /RATIONAL ROW.*F8C29.*F8C28/is);
  assert.match(html, /РАЦИОНАЛЬНАЯ СТРОКА.*F8C29.*F8C28/is);
  assert.match(html, /t.*v.*x.*y.*s.*F.*I/is);
  assert.match(html, /20\s*\/\s*\(n\s*\+\s*1\)/);
  assert.match(html, /MEASUREMENT TABLE.*CLOSED/is);
  assert.match(html, /EXTERNAL ACQUISITION.*OPEN/is);
  assert.doesNotMatch(html, /#print axioms|by\s+simp|structure\s+ExactRationalMeasurementRecord/);
});

test('F8C31D advances the public route', async () => {
  const route = await readFile(new URL('../app/route.ts', import.meta.url), 'utf8');
  assert.match(route, /public\/index\.html\?raw/);
  assert.match(route, /chertogi-razuma-research.kernelpanic888.chatgpt.site/);
});
