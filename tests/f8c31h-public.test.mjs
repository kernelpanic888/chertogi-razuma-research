import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

test('F8C31H public scene distinguishes readiness from an executed key ceremony', async () => {
  const html = await readFile(new URL('../public/index.html', import.meta.url), 'utf8');
  assert.match(html, /if-bs-f8c31h-operational-anchor-ceremony/);
  assert.match(html, /CEREMONY TOOL.*READY/is);
  assert.match(html, /OPERATIONAL ROOT.*NOT CREATED/is);
  assert.match(html, /EXTERNAL PUBLICATION.*NOT PERFORMED/is);
  assert.match(html, /A root cannot certify itself/i);
  assert.ok(html.indexOf('if-bs-f8c31g-identity-trust-chain') < html.indexOf('if-bs-f8c31h-operational-anchor-ceremony'));
  assert.doesNotMatch(html, /PRIVATE KEY-----/);
});

test('F8C31H advances the local public route', async () => {
  const route = await readFile(new URL('../app/page.tsx', import.meta.url), 'utf8');
  assert.match(route, /first-distinction-53/);
});
