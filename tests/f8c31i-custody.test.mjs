import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, readFile, rm, stat } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { assertOutsideWorkspace, generateEncryptedRoot, inspectEncryptedRoot, projectRoot, validatePassphrase } from '../verification/f8c31i/encrypted-offline-custody.mjs';

const passphrase = 'test-only passphrase with 36 characters!';

test('F8C31I rejects relative and workspace custody paths before writing', async () => {
  await assert.rejects(() => assertOutsideWorkspace('relative/key-dir'), /absolute/);
  await assert.rejects(() => assertOutsideWorkspace(path.join(projectRoot, 'private-key')), /outside the workspace/);
});

test('F8C31I rejects weak and mismatched passphrases', () => {
  assert.throws(() => validatePassphrase('short', 'short'), /24 characters/);
  assert.throws(() => validatePassphrase(passphrase, `${passphrase}x`), /confirmation mismatch/);
});

test('F8C31I atomically creates encrypted 0700/0600 custody outside the workspace', async t => {
  const parent = await mkdtemp(path.join(os.tmpdir(), 'ifbs31i-'));
  const keyDir = path.join(parent, 'root-custody');
  t.after(() => rm(parent, { recursive: true, force: true }));
  const generated = await generateEncryptedRoot({ keyDir, passphrase, confirmation: passphrase });
  const inspected = await inspectEncryptedRoot({ keyDir, passphrase });
  assert.equal(inspected.accepted, true);
  assert.equal(inspected.encrypted, true);
  assert.equal(inspected.decrypts, true);
  assert.equal(inspected.directoryMode, 0o700);
  assert.equal(inspected.privateKeyMode, 0o600);
  assert.equal(inspected.keyId, generated.receipt.rootKeyId);
  const privatePem = await readFile(path.join(keyDir, generated.receipt.privateKeyFile), 'utf8');
  assert.match(privatePem, /BEGIN ENCRYPTED PRIVATE KEY/);
  assert.doesNotMatch(privatePem, /BEGIN PRIVATE KEY-----/);
  assert.equal((await stat(keyDir)).mode & 0o777, 0o700);
});

test('F8C31I public receipt contains fingerprint but no passphrase', async t => {
  const parent = await mkdtemp(path.join(os.tmpdir(), 'ifbs31i-'));
  const keyDir = path.join(parent, 'root-custody');
  t.after(() => rm(parent, { recursive: true, force: true }));
  const { receipt } = await generateEncryptedRoot({ keyDir, passphrase, confirmation: passphrase });
  const receiptText = await readFile(path.join(keyDir, 'custody-receipt.json'), 'utf8');
  assert.match(receiptText, new RegExp(receipt.rootKeyId));
  assert.doesNotMatch(receiptText, new RegExp(passphrase.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')));
  assert.equal(JSON.parse(receiptText).passphraseStored, false);
});

test('F8C31I refuses overwrite and wrong-passphrase inspection', async t => {
  const parent = await mkdtemp(path.join(os.tmpdir(), 'ifbs31i-'));
  const keyDir = path.join(parent, 'root-custody');
  t.after(() => rm(parent, { recursive: true, force: true }));
  await generateEncryptedRoot({ keyDir, passphrase, confirmation: passphrase });
  await assert.rejects(() => generateEncryptedRoot({ keyDir, passphrase, confirmation: passphrase }), /overwrite is forbidden/);
  const inspected = await inspectEncryptedRoot({ keyDir, passphrase: `${passphrase}wrong` });
  assert.equal(inspected.accepted, false);
  assert.equal(inspected.decrypts, false);
});
