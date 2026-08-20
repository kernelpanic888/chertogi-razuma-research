import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

test('F8C31F public scene keeps content, signature and identity claims separate', async () => {
  const html = await readFile(new URL('../public/index.html', import.meta.url), 'utf8');
  assert.match(html, /if-bs-f8c31f-content-addressed-release/);
  assert.match(html, /CONTENT INTEGRITY.*CLOSED/is);
  assert.match(html, /SIGNATURE VALIDITY.*CLOSED/is);
  assert.match(html, /IDENTITY BINDING.*OPEN/is);
  assert.match(html, /Accept\s*:=\s*C\s*∧\s*P/);
  assert.doesNotMatch(html, /node:crypto/);
  assert.ok(
    html.indexOf('if-bs-f8c31e-canonical-replay') <
      html.indexOf('if-bs-f8c31f-content-addressed-release'),
    'F8C31F must follow the F8C31E content it addresses',
  );
});

test('F8C31F advances the local public route', async () => {
  const route = await readFile(new URL('../app/route.ts', import.meta.url), 'utf8');
  assert.match(route, /public\/index\.html\?raw/);
  assert.match(route, /chertogi-razuma-research.kernelpanic888.chatgpt.site/);
});
