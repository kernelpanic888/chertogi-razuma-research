import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

const htmlPath = new URL('../public/index.html', import.meta.url);

test('F8C31C public scene exposes the proved metric transport without Lean source', async () => {
  const html = await readFile(htmlPath, 'utf8');
  assert.match(html, /if-bs-f8c31c-metric-transport/);
  assert.match(html, /20\s*\/\s*\(n\s*\+\s*1\)/);
  assert.match(html, /10G/);
  assert.match(html, /EXACT DIAMOND.*NET.*CLOSED/is);
  assert.match(html, /ТОЧНАЯ.*СЕТЬ.*РОМБА.*ЗАМКНУТА/is);
  assert.match(html, /FINITE MEASUREMENT RECORDS.*OPEN/is);
  assert.doesNotMatch(html, /#print axioms|by\s+nlinarith|theorem\s+stereographicDiamondLift_dist_le_ten/);
});

test('F8C31C advances the public route', async () => {
  const route = await readFile(new URL('../app/page.tsx', import.meta.url), 'utf8');
  assert.match(route, /first-distinction-53/);
});
