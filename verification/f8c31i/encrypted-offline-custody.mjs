import { createHash, createPrivateKey, createPublicKey, generateKeyPairSync } from 'node:crypto';
import { access, chmod, mkdir, readFile, realpath, rename, rm, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
export const projectRoot = path.resolve(here, '../..');
const canonical = value => `${JSON.stringify(value, null, 2)}\n`;
const fingerprint = publicKey => {
  const der = publicKey.export({ type: 'spki', format: 'der' });
  return `sha256:${createHash('sha256').update(der).digest('hex')}`;
};

async function exists(target) {
  try { await access(target); return true; } catch { return false; }
}

async function canonicalDestination(target) {
  if (!path.isAbsolute(target)) throw new Error('key directory must be absolute');
  const absolute = path.resolve(target);
  let ancestor = absolute;
  while (!(await exists(ancestor))) {
    const parent = path.dirname(ancestor);
    if (parent === ancestor) throw new Error('no existing destination ancestor');
    ancestor = parent;
  }
  const realAncestor = await realpath(ancestor);
  return path.join(realAncestor, path.relative(ancestor, absolute));
}

export async function assertOutsideWorkspace(keyDir, workspaceRoot = projectRoot) {
  const [destination, workspace] = await Promise.all([canonicalDestination(keyDir), realpath(workspaceRoot)]);
  const relative = path.relative(workspace, destination);
  if (relative === '' || (!relative.startsWith('..') && !path.isAbsolute(relative))) throw new Error('operational key storage must be outside the workspace');
  return destination;
}

export function validatePassphrase(passphrase, confirmation) {
  if (typeof passphrase !== 'string' || passphrase.length < 24 || passphrase.trim().length < 20) throw new Error('passphrase must contain at least 24 characters');
  if (passphrase !== confirmation) throw new Error('passphrase confirmation mismatch');
  return true;
}

export async function generateEncryptedRoot({ keyDir, passphrase, confirmation, workspaceRoot = projectRoot }) {
  validatePassphrase(passphrase, confirmation);
  const destination = await assertOutsideWorkspace(keyDir, workspaceRoot);
  if (await exists(destination)) throw new Error('custody directory already exists; overwrite is forbidden');
  const parent = path.dirname(destination);
  const stage = path.join(parent, `.ifbs-custody-stage-${process.pid}-${Date.now()}`);
  await mkdir(stage, { mode: 0o700 });
  try {
    const { publicKey, privateKey } = generateKeyPairSync('ed25519');
    const encryptedPrivatePem = privateKey.export({ type: 'pkcs8', format: 'pem', cipher: 'aes-256-cbc', passphrase });
    const publicPem = publicKey.export({ type: 'spki', format: 'pem' });
    const keyId = fingerprint(publicKey);
    const receipt = {
      schema: 'IFBS31I-RECEIPT/1',
      profile: 'encrypted-offline-file',
      algorithm: 'ed25519',
      cipher: 'aes-256-cbc',
      rootKeyId: keyId,
      privateKeyFile: 'identity-root.private.encrypted.pem',
      publicKeyFile: 'identity-root.public.pem',
      directoryMode: '0700',
      privateKeyMode: '0600',
      overwriteAllowed: false,
      passphraseStored: false,
    };
    await writeFile(path.join(stage, receipt.privateKeyFile), encryptedPrivatePem, { flag: 'wx', mode: 0o600 });
    await writeFile(path.join(stage, receipt.publicKeyFile), publicPem, { flag: 'wx', mode: 0o644 });
    await writeFile(path.join(stage, 'custody-receipt.json'), canonical(receipt), { flag: 'wx', mode: 0o644 });
    await chmod(stage, 0o700);
    await chmod(path.join(stage, receipt.privateKeyFile), 0o600);
    await rename(stage, destination);
    return { destination, receipt };
  } catch (error) {
    await rm(stage, { recursive: true, force: true });
    throw error;
  }
}

export async function inspectEncryptedRoot({ keyDir, passphrase, workspaceRoot = projectRoot }) {
  const destination = await assertOutsideWorkspace(keyDir, workspaceRoot);
  const receipt = JSON.parse(await readFile(path.join(destination, 'custody-receipt.json'), 'utf8'));
  const [directoryStat, privateStat, privatePem, publicPem] = await Promise.all([
    stat(destination),
    stat(path.join(destination, receipt.privateKeyFile)),
    readFile(path.join(destination, receipt.privateKeyFile), 'utf8'),
    readFile(path.join(destination, receipt.publicKeyFile), 'utf8'),
  ]);
  const encrypted = /BEGIN ENCRYPTED PRIVATE KEY/.test(privatePem) && !/BEGIN PRIVATE KEY-----/.test(privatePem);
  let decrypts = false, keyId = null;
  try {
    const privateKey = createPrivateKey({ key: privatePem, format: 'pem', passphrase });
    keyId = fingerprint(createPublicKey(privateKey));
    decrypts = keyId === receipt.rootKeyId && keyId === fingerprint(createPublicKey(publicPem));
  } catch {
    decrypts = false;
  }
  const directoryMode = directoryStat.mode & 0o777, privateKeyMode = privateStat.mode & 0o777;
  const accepted = encrypted && decrypts && directoryMode === 0o700 && privateKeyMode === 0o600 && receipt.passphraseStored === false && receipt.overwriteAllowed === false;
  return { accepted, encrypted, decrypts, directoryMode, privateKeyMode, keyId, receipt };
}

async function main() {
  const [command, keyDir] = process.argv.slice(2);
  if (!command || !keyDir) throw new Error('usage: encrypted-offline-custody.mjs preflight|generate|inspect ABSOLUTE_KEY_DIR');
  if (command === 'preflight') {
    console.log(JSON.stringify({ ok: true, destination: await assertOutsideWorkspace(keyDir), secretCreated: false }));
    return;
  }
  const passphrase = process.env.IFBS_ROOT_PASSPHRASE, confirmation = process.env.IFBS_ROOT_PASSPHRASE_CONFIRM;
  if (command === 'generate') {
    const result = await generateEncryptedRoot({ keyDir, passphrase, confirmation });
    console.log(JSON.stringify({ ok: true, destination: result.destination, rootKeyId: result.receipt.rootKeyId, passphraseStored: false }));
    return;
  }
  if (command === 'inspect') {
    const result = await inspectEncryptedRoot({ keyDir, passphrase });
    console.log(JSON.stringify(result));
    if (!result.accepted) process.exitCode = 1;
    return;
  }
  throw new Error(`unknown command: ${command}`);
}

if (process.argv[1] === fileURLToPath(import.meta.url)) await main();
