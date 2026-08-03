import test from 'node:test';
import assert from 'node:assert/strict';
import { generateKeyPairSync } from 'node:crypto';
import { fingerprintPublicKey, prepareWitness, verifyWitness } from '../verification/f8c31h/ceremony.mjs';

const publicPem = pair => pair.publicKey.export({ type: 'spki', format: 'pem' });

test('F8C31H prepares a canonical public-only witness candidate', () => {
  const pair = generateKeyPairSync('ed25519'), pem = publicPem(pair);
  const witness = prepareWitness({ publicKeyPem: pem, publicationUri: 'https://example.invalid/aleksey/root-fingerprint' });
  assert.equal(`${JSON.stringify(JSON.parse(witness), null, 2)}\n`, witness);
  assert.match(witness, new RegExp(fingerprintPublicKey(pem)));
  assert.doesNotMatch(witness, /PRIVATE KEY/);
});

test('F8C31H structurally accepts an independently located matching witness copy', () => {
  const pair = generateKeyPairSync('ed25519'), pem = publicPem(pair);
  const witnessText = prepareWitness({ publicKeyPem: pem, publicationUri: 'https://example.invalid/aleksey/root-fingerprint' });
  const result = verifyWitness({ witnessText, publicKeyPem: pem });
  assert.equal(result.accepted, true);
  assert.equal(result.independentSource, true);
  assert.equal(result.externallyObserved, false);
});

test('F8C31H rejects a self-witness hosted by the research release', () => {
  const pair = generateKeyPairSync('ed25519'), pem = publicPem(pair);
  const witnessText = prepareWitness({ publicKeyPem: pem, publicationUri: 'https://chertogi-razuma-research.kernelpanic888.chatgpt.site/root-fingerprint' });
  const result = verifyWitness({ witnessText, publicKeyPem: pem });
  assert.equal(result.accepted, false);
  assert.equal(result.independentSource, false);
});

test('F8C31H rejects a matching witness text checked against another public key', () => {
  const first = generateKeyPairSync('ed25519'), second = generateKeyPairSync('ed25519');
  const witnessText = prepareWitness({ publicKeyPem: publicPem(first), publicationUri: 'https://example.invalid/aleksey/root-fingerprint' });
  const result = verifyWitness({ witnessText, publicKeyPem: publicPem(second) });
  assert.equal(result.accepted, false);
  assert.equal(result.fingerprintMatches, false);
});

test('F8C31H refuses private key material at the ceremony boundary', () => {
  const pair = generateKeyPairSync('ed25519');
  const privatePem = pair.privateKey.export({ type: 'pkcs8', format: 'pem' });
  assert.throws(() => fingerprintPublicKey(privatePem), /private key material is forbidden/);
});
