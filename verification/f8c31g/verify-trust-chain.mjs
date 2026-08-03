import { createHash, createPublicKey, verify } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { projectRoot, verifyRelease as verifyAddressedRelease } from '../f8c31f/verify-release.mjs';

const digest = bytes => createHash('sha256').update(bytes).digest();
const address = bytes => `sha256:${digest(bytes).toString('hex')}`;
const canonical = value => `${JSON.stringify(value, null, 2)}\n`;

function safePath(relativePath) {
  if (typeof relativePath !== 'string' || relativePath.startsWith('/') || relativePath.includes('\\')) throw new Error(`unsafe path: ${relativePath}`);
  const normalized = path.posix.normalize(relativePath);
  if (normalized === '..' || normalized.startsWith('../') || normalized !== relativePath) throw new Error(`unsafe path: ${relativePath}`);
  return normalized;
}

async function load(root, relativePath, overrides) {
  const safe = safePath(relativePath);
  if (overrides.has(safe)) return Buffer.from(overrides.get(safe));
  return readFile(path.join(root, safe));
}

async function document(root, relativePath, overrides, failures) {
  const bytes = await load(root, relativePath, overrides);
  const value = JSON.parse(bytes.toString('utf8'));
  if (bytes.toString('utf8') !== canonical(value)) failures.push(`noncanonical document: ${relativePath}`);
  return { bytes, value, digest: digest(bytes), address: address(bytes) };
}

async function publicKey(root, relativePath, overrides) {
  const key = createPublicKey(await load(root, relativePath, overrides));
  const der = key.export({ type: 'spki', format: 'der' });
  return { key, keyId: address(der) };
}

async function signature(root, relativePath, overrides) {
  return Buffer.from((await load(root, relativePath, overrides)).toString('utf8').trim(), 'base64');
}

export async function verifyTrustChain({
  root = projectRoot,
  trustedRootKeyId = null,
  overrides = new Map(),
  release2Path = 'verification/f8c31g/release-2.json',
  release2SignaturePath = 'verification/f8c31g/release-2.signature.base64',
} = {}) {
  const failures = [], contentFailures = [];
  try {
    const priorContent = await verifyAddressedRelease({ root, overrides });
    const [anchor, release1, rotation, release2] = await Promise.all([
      document(root, 'verification/f8c31g/identity-anchor.json', overrides, failures),
      document(root, 'verification/f8c31g/release-1.json', overrides, failures),
      document(root, 'verification/f8c31g/rotation-1.json', overrides, failures),
      document(root, release2Path, overrides, failures),
    ]);
    const [rootKey, keyA, keyB] = await Promise.all([
      publicKey(root, 'verification/f8c31g/identity-root-public.pem', overrides),
      publicKey(root, 'verification/f8c31g/release-key-a-public.pem', overrides),
      publicKey(root, 'verification/f8c31g/release-key-b-public.pem', overrides),
    ]);
    const [anchorSig, release1Sig, rotationRootSig, rotationOldSig, rotationNewSig, release2Sig] = await Promise.all([
      signature(root, 'verification/f8c31g/identity-anchor.signature.base64', overrides),
      signature(root, 'verification/f8c31g/release-1.signature.base64', overrides),
      signature(root, 'verification/f8c31g/rotation-1.root.signature.base64', overrides),
      signature(root, 'verification/f8c31g/rotation-1.old.signature.base64', overrides),
      signature(root, 'verification/f8c31g/rotation-1.new.signature.base64', overrides),
      signature(root, release2SignaturePath, overrides),
    ]);

    const anchorSignatureValid = verify(null, anchor.digest, rootKey.key, anchorSig);
    const release1SignatureValid = verify(null, release1.digest, keyA.key, release1Sig);
    const rotationSignatures = {
      root: verify(null, rotation.digest, rootKey.key, rotationRootSig),
      old: verify(null, rotation.digest, keyA.key, rotationOldSig),
      next: verify(null, rotation.digest, keyB.key, rotationNewSig),
    };
    const claimedRelease2Key = release2.value.signerKeyId === keyA.keyId ? keyA : release2.value.signerKeyId === keyB.keyId ? keyB : null;
    const release2SignatureValid = claimedRelease2Key ? verify(null, release2.digest, claimedRelease2Key.key, release2Sig) : false;

    const release2Content = await load(root, release2.value.contentPath, overrides);
    let release2ContentValid = address(release2Content) === release2.value.contentAddress;
    let release2Artifacts = 0;
    if (!release2ContentValid) contentFailures.push('release 2 content-manifest address mismatch');
    try {
      const contentManifest = JSON.parse(release2Content.toString('utf8'));
      if (release2Content.toString('utf8') !== canonical(contentManifest)) contentFailures.push('release 2 content manifest is not canonical');
      if (contentManifest.schema !== 'IFBS31G-CONTENT/1' || contentManifest.releaseId !== 'first-distinction-51' || !Array.isArray(contentManifest.artifacts)) {
        contentFailures.push('release 2 content manifest schema mismatch');
      }
      const seen = new Set();
      release2Artifacts = contentManifest.artifacts?.length ?? 0;
      for (const artifact of contentManifest.artifacts ?? []) {
        const artifactPath = safePath(artifact.path);
        if (seen.has(artifactPath)) contentFailures.push(`duplicate release 2 artifact: ${artifactPath}`);
        seen.add(artifactPath);
        const bytes = await load(root, artifactPath, overrides);
        if (bytes.length !== artifact.bytes) contentFailures.push(`release 2 byte count mismatch: ${artifactPath}`);
        if (address(bytes) !== artifact.sha256) contentFailures.push(`release 2 digest mismatch: ${artifactPath}`);
      }
    } catch (error) {
      contentFailures.push(error instanceof Error ? error.message : String(error));
    }
    release2ContentValid = release2ContentValid && contentFailures.length === 0;
    const revokedAtRelease2 = rotation.value.revokesFromAtSequence <= release2.value.sequence && release2.value.signerKeyId === rotation.value.fromKeyId;
    const release2KeyTrusted = release2.value.signerKeyId === rotation.value.toKeyId && !revokedAtRelease2;

    const structuralChecks = [
      anchor.value.schema === 'IFBS31G-ANCHOR/1',
      anchor.value.subjectId === 'https://orcid.org/0009-0006-8717-0492',
      anchor.value.rootKeyId === rootKey.keyId,
      anchor.value.activeReleaseKeyId === keyA.keyId,
      release1.value.schema === 'IFBS31G-RELEASE/1' && release1.value.sequence === 1,
      release1.value.signerKeyId === keyA.keyId,
      release1.value.contentAddress === priorContent.content.manifestSha256,
      rotation.value.schema === 'IFBS31G-ROTATION/1' && rotation.value.sequence === 1,
      rotation.value.rootKeyId === rootKey.keyId,
      rotation.value.fromKeyId === keyA.keyId,
      rotation.value.toKeyId === keyB.keyId,
      rotation.value.previousReleaseDigest === release1.address,
      rotation.value.revokesFromAtSequence === 2,
      release2.value.schema === 'IFBS31G-RELEASE/1' && release2.value.sequence === 2,
      release2.value.previousReleaseDigest === release1.address,
      release2.value.rotationDigest === rotation.address,
    ];
    if (structuralChecks.some(value => !value)) failures.push('chain relation mismatch');
    if (!anchorSignatureValid) failures.push('anchor signature invalid');
    if (!release1SignatureValid) failures.push('release 1 signature invalid');
    if (!rotationSignatures.root || !rotationSignatures.old || !rotationSignatures.next) failures.push('rotation lacks three valid approvals');
    if (!release2SignatureValid) failures.push('release 2 signature invalid');
    if (!release2KeyTrusted) failures.push(revokedAtRelease2 ? 'release 2 uses revoked key' : 'release 2 key is not active');
    const content = { ok: priorContent.ok && release2ContentValid, release1: priorContent.ok, release2: release2ContentValid, release2Artifacts, failures: contentFailures };
    const continuity = {
      ok: failures.length === 0,
      anchorSignatureValid,
      release1SignatureValid,
      rotationSignatures,
      release2SignatureValid,
      release2KeyTrusted,
      revokedKeyId: rotation.value.fromKeyId,
      activeKeyId: rotation.value.toKeyId,
      failures,
    };
    const externallyAnchored = trustedRootKeyId !== null && trustedRootKeyId === rootKey.keyId;
    const identity = {
      subjectName: anchor.value.subjectName,
      subjectId: anchor.value.subjectId,
      rootKeyId: rootKey.keyId,
      externallyAnchored,
      recognizedAuthor: continuity.ok && externallyAnchored,
    };
    return { ok: content.ok && continuity.ok, content, continuity, identity };
  } catch (error) {
    failures.push(error instanceof Error ? error.message : String(error));
    return {
      ok: false,
      content: { ok: false, release1: false, release2: false, release2Artifacts: 0, failures: contentFailures },
      continuity: { ok: false, anchorSignatureValid: false, release1SignatureValid: false, rotationSignatures: { root: false, old: false, next: false }, release2SignatureValid: false, release2KeyTrusted: false, revokedKeyId: null, activeKeyId: null, failures },
      identity: { subjectName: null, subjectId: null, rootKeyId: null, externallyAnchored: false, recognizedAuthor: false },
    };
  }
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const result = await verifyTrustChain();
  console.log(JSON.stringify(result));
  if (!result.ok) process.exitCode = 1;
}
