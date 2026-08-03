import { createHash, createPublicKey, verify } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { verifyDocument } from '../f8c31e/verify.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
export const projectRoot = path.resolve(here, '../..');
const manifestPath = 'verification/f8c31f/release-manifest.json';
const attestationPath = 'verification/f8c31f/release-attestation.json';

const digest = bytes => createHash('sha256').update(bytes).digest();
const hex = bytes => bytes.toString('hex');
const canonicalJson = value => `${JSON.stringify(value, null, 2)}\n`;

function safePath(relativePath) {
  if (typeof relativePath !== 'string' || relativePath.startsWith('/') || relativePath.includes('\\')) {
    throw new Error(`unsafe artifact path: ${relativePath}`);
  }
  const normalized = path.posix.normalize(relativePath);
  if (normalized === '..' || normalized.startsWith('../') || normalized !== relativePath) {
    throw new Error(`unsafe artifact path: ${relativePath}`);
  }
  return normalized;
}

async function loadBytes(root, relativePath, overrides) {
  const safe = safePath(relativePath);
  if (overrides.has(safe)) return Buffer.from(overrides.get(safe));
  return readFile(path.join(root, safe));
}

export async function verifyRelease({ root = projectRoot, overrides = new Map() } = {}) {
  const contentFailures = [], provenanceFailures = [];
  try {
    const [manifestBytes, attestationBytes] = await Promise.all([
      loadBytes(root, manifestPath, overrides),
      loadBytes(root, attestationPath, overrides),
    ]);
    const manifest = JSON.parse(manifestBytes.toString('utf8'));
    const attestation = JSON.parse(attestationBytes.toString('utf8'));

    if (manifestBytes.toString('utf8') !== canonicalJson(manifest)) contentFailures.push('manifest is not canonical JSON');
    if (manifest.schema !== 'IFBS31F/1' || manifest.releaseId !== 'first-distinction-50') contentFailures.push('manifest schema or release mismatch');
    if (manifest.hashAlgorithm !== 'sha256' || !Array.isArray(manifest.artifacts) || manifest.artifacts.length === 0) contentFailures.push('unsupported content contract');

    const manifestDigest = digest(manifestBytes);
    const addressed = `sha256:${hex(manifestDigest)}`;
    if (attestation.manifest !== manifestPath || attestation.manifestSha256 !== addressed) contentFailures.push('manifest address mismatch');

    const seen = new Set();
    for (const artifact of manifest.artifacts ?? []) {
      const artifactPath = safePath(artifact.path);
      if (seen.has(artifactPath)) contentFailures.push(`duplicate artifact: ${artifactPath}`);
      seen.add(artifactPath);
      const bytes = await loadBytes(root, artifactPath, overrides);
      if (bytes.length !== artifact.bytes) contentFailures.push(`byte count mismatch: ${artifactPath}`);
      if (`sha256:${hex(digest(bytes))}` !== artifact.sha256) contentFailures.push(`digest mismatch: ${artifactPath}`);
    }

    const fixtureBytes = await loadBytes(root, 'verification/f8c31e/fixture.ifbs', overrides);
    const replay = verifyDocument(fixtureBytes.toString('utf8'));
    if (!replay.ok) contentFailures.push('canonical replay rejected');

    if (attestation.schema !== 'IFBS31F-SIGNATURE/1' || attestation.signatureAlgorithm !== 'ed25519') provenanceFailures.push('attestation schema or algorithm mismatch');
    const [publicKeyBytes, signatureBytes] = await Promise.all([
      loadBytes(root, safePath(attestation.publicKey), overrides),
      loadBytes(root, safePath(attestation.signature), overrides),
    ]);
    const publicKey = createPublicKey(publicKeyBytes);
    const keyDer = publicKey.export({ type: 'spki', format: 'der' });
    const keyId = `sha256:${hex(digest(keyDer))}`;
    if (keyId !== attestation.signerKeyId || keyId !== manifest.signerKeyId) provenanceFailures.push('signer key id mismatch');
    const signature = Buffer.from(signatureBytes.toString('utf8').trim(), 'base64');
    if (!verify(null, manifestDigest, publicKey, signature)) provenanceFailures.push('signature invalid');

    const content = {
      ok: contentFailures.length === 0,
      manifestSha256: addressed,
      artifacts: manifest.artifacts?.length ?? 0,
      replay: replay.ok === true,
      failures: contentFailures,
    };
    const provenance = {
      ok: provenanceFailures.length === 0,
      signerKeyId: keyId,
      signatureValid: provenanceFailures.length === 0,
      identityAnchored: false,
      failures: provenanceFailures,
    };
    return { ok: content.ok && provenance.ok, content, provenance };
  } catch (error) {
    contentFailures.push(error instanceof Error ? error.message : String(error));
    return {
      ok: false,
      content: { ok: false, manifestSha256: null, artifacts: 0, replay: false, failures: contentFailures },
      provenance: { ok: false, signerKeyId: null, signatureValid: false, identityAnchored: false, failures: provenanceFailures },
    };
  }
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const result = await verifyRelease();
  console.log(JSON.stringify(result));
  if (!result.ok) process.exitCode = 1;
}
