import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { generateDocument, verifyDocument } from '../verification/f8c31e/verify.mjs';

const fixtureUrl = new URL('../verification/f8c31e/fixture.ifbs', import.meta.url);

test('F8C31E fixture is canonical and independently replayable', async () => {
  const fixture = (await readFile(fixtureUrl, 'utf8')).trimEnd();
  assert.equal(fixture, generateDocument(2));
  assert.deepEqual(verifyDocument(fixture), {
    ok: true,
    schema: 'IFBS31E/1',
    level: 2,
    rows: 32,
    amplitude: '1/2',
  });
});

test('F8C31E verifier rejects one-field corruption', async () => {
  const fixture = (await readFile(fixtureUrl, 'utf8')).trimEnd();
  const corrupted = fixture.replace('|9/4|4/9|0/1|0/1', '|9/4|5/9|0/1|0/1');
  assert.notEqual(corrupted, fixture);
  assert.equal(verifyDocument(corrupted).ok, false);
});
