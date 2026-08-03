import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { verifyTrustChain } from '../verification/f8c31g/verify-trust-chain.mjs';

test('F8C31G verifies two releases and three-party key rotation without claiming identity', async () => {
  const result = await verifyTrustChain();
  assert.equal(result.ok, true);
  assert.equal(result.content.ok, true);
  assert.equal(result.content.release2Artifacts, 5);
  assert.equal(result.continuity.ok, true);
  assert.deepEqual(result.continuity.rotationSignatures, { root: true, old: true, next: true });
  assert.equal(result.continuity.release2KeyTrusted, true);
  assert.equal(result.identity.externallyAnchored, false);
  assert.equal(result.identity.recognizedAuthor, false);
});

test('F8C31G recognizes the author only from an independently supplied root fingerprint', async () => {
  const fingerprint = (await readFile(new URL('../verification/f8c31g/anchor-fingerprint.txt', import.meta.url), 'utf8')).trim();
  const accepted = await verifyTrustChain({ trustedRootKeyId: fingerprint });
  const rejected = await verifyTrustChain({ trustedRootKeyId: `sha256:${'0'.repeat(64)}` });
  assert.equal(accepted.identity.externallyAnchored, true);
  assert.equal(accepted.identity.recognizedAuthor, true);
  assert.equal(rejected.ok, true);
  assert.equal(rejected.identity.recognizedAuthor, false);
});

test('F8C31G rejects a modified rotation record', async () => {
  const relative = 'verification/f8c31g/rotation-1.json';
  const original = await readFile(new URL(`../${relative}`, import.meta.url), 'utf8');
  const changed = original.replace('"sequence": 1', '"sequence": 9');
  assert.notEqual(changed, original);
  const result = await verifyTrustChain({ overrides: new Map([[relative, changed]]) });
  assert.equal(result.ok, false);
  assert.equal(result.continuity.ok, false);
  assert.equal(result.continuity.rotationSignatures.root, false);
});

test('F8C31G rejects one changed release-2 artifact without breaking key continuity', async () => {
  const relative = 'research/interface-foundations-v0.1/INTRINSIC_NONRADIAL_SHEAR_IDENTITY_TRUST_CHAIN.md';
  const original = await readFile(new URL(`../${relative}`, import.meta.url), 'utf8');
  const result = await verifyTrustChain({ overrides: new Map([[relative, `${original}\nchanged\n`]]) });
  assert.equal(result.ok, false);
  assert.equal(result.content.ok, false);
  assert.equal(result.continuity.ok, true);
});

test('F8C31G rejects a cryptographically valid release signed by the revoked old key', async () => {
  const result = await verifyTrustChain({
    release2Path: 'verification/f8c31g/release-2-revoked.json',
    release2SignaturePath: 'verification/f8c31g/release-2-revoked.signature.base64',
  });
  assert.equal(result.ok, false);
  assert.equal(result.continuity.release2SignatureValid, true);
  assert.equal(result.continuity.release2KeyTrusted, false);
  assert.match(result.continuity.failures.join(' '), /revoked key/);
});
