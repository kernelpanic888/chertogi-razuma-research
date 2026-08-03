import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { projectRoot, verifyRelease } from '../verification/f8c31f/verify-release.mjs';

test('F8C31F accepts the addressed artifacts and Ed25519 attestation independently', async () => {
  const result = await verifyRelease();
  assert.equal(result.ok, true);
  assert.equal(result.content.ok, true);
  assert.equal(result.content.artifacts, 9);
  assert.equal(result.content.replay, true);
  assert.equal(result.provenance.ok, true);
  assert.equal(result.provenance.signatureValid, true);
  assert.equal(result.provenance.identityAnchored, false);
});

test('F8C31F keeps a valid signature while rejecting changed artifact bytes', async () => {
  const relative = 'verification/f8c31e/fixture.ifbs';
  const original = await readFile(new URL(`../${relative}`, import.meta.url));
  const changed = Buffer.from(original.toString('utf8').replace('|9/4|4/9|', '|9/4|5/9|'));
  assert.notDeepEqual(changed, original);
  const result = await verifyRelease({ root: projectRoot, overrides: new Map([[relative, changed]]) });
  assert.equal(result.ok, false);
  assert.equal(result.content.ok, false);
  assert.equal(result.provenance.ok, true);
});

test('F8C31F keeps valid content while rejecting a changed signature', async () => {
  const relative = 'verification/f8c31f/release-signature.base64';
  const original = (await readFile(new URL(`../${relative}`, import.meta.url), 'utf8')).trim();
  const changed = `${original[0] === 'A' ? 'B' : 'A'}${original.slice(1)}\n`;
  const result = await verifyRelease({ root: projectRoot, overrides: new Map([[relative, changed]]) });
  assert.equal(result.ok, false);
  assert.equal(result.content.ok, true);
  assert.equal(result.provenance.ok, false);
});
