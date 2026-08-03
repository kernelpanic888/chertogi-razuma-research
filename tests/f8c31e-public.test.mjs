import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

const htmlPath = new URL('../public/index.html', import.meta.url);

test('F8C31E public scene explains canonical replay without implementation source', async () => {
  const html = await readFile(htmlPath, 'utf8');
  assert.match(html, /if-bs-f8c31e-canonical-replay/);
  assert.match(html, /IFBS31E\/1/);
  assert.match(html, /REDUCED FRACTION.*RECOMPUTE.*REJECT/is);
  assert.match(html, /СОКРАЩЁННАЯ ДРОБЬ.*ПЕРЕСЧЁТ.*ОТКЛОНЕНИЕ/is);
  assert.match(html, /32\s*\/\s*32/);
  assert.match(html, /CANONICAL REPLAY.*CLOSED/is);
  assert.match(html, /SIGNED PROVENANCE.*OPEN/is);
  assert.doesNotMatch(html, /BigInt|Rat\.mk'|replayWireEnvelopeAccepted|node:fs/);
});

test('F8C31E advances the public route', async () => {
  const route = await readFile(new URL('../app/page.tsx', import.meta.url), 'utf8');
  assert.match(route, /first-distinction-53/);
});
