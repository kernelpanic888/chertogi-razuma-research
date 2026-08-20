import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

test('F8C31I public scene shows safe custody readiness without claiming key generation', async () => {
  const html = await readFile(new URL('../public/index.html', import.meta.url), 'utf8');
  assert.match(html, /if-bs-f8c31i-encrypted-offline-custody/);
  assert.match(html, /CUSTODY PREFLIGHT.*CLOSED/is);
  assert.match(html, /OPERATIONAL SECRET.*NOT GENERATED/is);
  assert.match(html, /EXTERNAL WITNESS.*OPEN/is);
  assert.match(html, /0700.*0600/is);
  assert.ok(html.indexOf('if-bs-f8c31h-operational-anchor-ceremony') < html.indexOf('if-bs-f8c31i-encrypted-offline-custody'));
  assert.doesNotMatch(html, /BEGIN (?:ENCRYPTED )?PRIVATE KEY/);
});

test('F8C31I is served through the canonical public route', async () => {
  const route = await readFile(new URL('../app/route.ts', import.meta.url), 'utf8');
  assert.match(route, /public\/index\.html\?raw/);
  assert.match(route, /chertogi-razuma-research\.kernelpanic888\.chatgpt\.site/);
});
