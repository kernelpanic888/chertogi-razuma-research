import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

test('F8C31G public scene shows continuity, revocation and the external identity boundary', async () => {
  const html = await readFile(new URL('../public/index.html', import.meta.url), 'utf8');
  assert.match(html, /if-bs-f8c31g-identity-trust-chain/);
  assert.match(html, /CHAIN CONTINUITY.*CLOSED/is);
  assert.match(html, /OLD KEY REVOKED.*CLOSED/is);
  assert.match(html, /EXTERNAL IDENTITY WITNESS.*OPEN/is);
  assert.match(html, /Sigroot\s*∧\s*Sigold\s*∧\s*Signew/i);
  assert.ok(html.indexOf('if-bs-f8c31f-content-addressed-release') < html.indexOf('if-bs-f8c31g-identity-trust-chain'));
  assert.doesNotMatch(html, /node:crypto/);
});

test('F8C31G is served through the canonical public route', async () => {
  const route = await readFile(new URL('../app/route.ts', import.meta.url), 'utf8');
  assert.match(route, /public\/index\.html\?raw/);
  assert.match(route, /chertogi-razuma-research\.kernelpanic888\.chatgpt\.site/);
});
