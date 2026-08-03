import { createHash, createPublicKey } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';

export const defaultPolicy = Object.freeze({
  schema: 'IFBS31H-POLICY/1',
  subjectName: 'Aleksey Salkutsan',
  subjectId: 'https://orcid.org/0009-0006-8717-0492',
  forbiddenWitnessHosts: ['chertogi-razuma-research.kernelpanic888.chatgpt.site'],
});

const canonical = value => `${JSON.stringify(value, null, 2)}\n`;

export function fingerprintPublicKey(publicKeyPem) {
  const text = Buffer.from(publicKeyPem).toString('utf8');
  if (/PRIVATE KEY/.test(text)) throw new Error('private key material is forbidden');
  const publicKey = createPublicKey(text);
  const der = publicKey.export({ type: 'spki', format: 'der' });
  return `sha256:${createHash('sha256').update(der).digest('hex')}`;
}

export function prepareWitness({ publicKeyPem, publicationUri, policy = defaultPolicy }) {
  const rootKeyId = fingerprintPublicKey(publicKeyPem);
  const witness = {
    schema: 'IFBS31H-WITNESS/1',
    subjectName: policy.subjectName,
    subjectId: policy.subjectId,
    rootKeyId,
    observedRootKeyId: rootKeyId,
    publicationUri,
    sourceIndependent: true,
  };
  return canonical(witness);
}

export function verifyWitness({ witnessText, publicKeyPem, policy = defaultPolicy }) {
  const failures = [];
  try {
    const witness = JSON.parse(witnessText);
    if (witnessText !== canonical(witness)) failures.push('witness is not canonical JSON');
    const fingerprint = fingerprintPublicKey(publicKeyPem);
    if (witness.schema !== 'IFBS31H-WITNESS/1') failures.push('witness schema mismatch');
    if (witness.subjectName !== policy.subjectName || witness.subjectId !== policy.subjectId) failures.push('subject mismatch');
    if (witness.rootKeyId !== fingerprint || witness.observedRootKeyId !== fingerprint) failures.push('root fingerprint mismatch');
    let independentSource = false;
    try {
      const uri = new URL(witness.publicationUri);
      independentSource = uri.protocol === 'https:' && !policy.forbiddenWitnessHosts.includes(uri.hostname) && witness.sourceIndependent === true;
    } catch {
      independentSource = false;
    }
    if (!independentSource) failures.push('witness source is not independent');
    return {
      accepted: failures.length === 0,
      fingerprint,
      subjectMatches: witness.subjectName === policy.subjectName && witness.subjectId === policy.subjectId,
      fingerprintMatches: witness.rootKeyId === fingerprint && witness.observedRootKeyId === fingerprint,
      independentSource,
      externallyObserved: false,
      failures,
    };
  } catch (error) {
    failures.push(error instanceof Error ? error.message : String(error));
    return { accepted: false, fingerprint: null, subjectMatches: false, fingerprintMatches: false, independentSource: false, externallyObserved: false, failures };
  }
}

async function main() {
  const [command, publicKeyPath, recordPathOrUri] = process.argv.slice(2);
  if (!command || !publicKeyPath) throw new Error('usage: ceremony.mjs fingerprint|prepare|verify PUBLIC_KEY [URI|WITNESS]');
  const publicKeyPem = await readFile(publicKeyPath);
  if (command === 'fingerprint') {
    console.log(fingerprintPublicKey(publicKeyPem));
    return;
  }
  if (command === 'prepare') {
    if (!recordPathOrUri) throw new Error('publication URI is required');
    process.stdout.write(prepareWitness({ publicKeyPem, publicationUri: recordPathOrUri }));
    return;
  }
  if (command === 'verify') {
    if (!recordPathOrUri) throw new Error('witness path is required');
    const result = verifyWitness({ witnessText: await readFile(recordPathOrUri, 'utf8'), publicKeyPem });
    console.log(JSON.stringify(result));
    if (!result.accepted) process.exitCode = 1;
    return;
  }
  throw new Error(`unknown command: ${command}`);
}

if (process.argv[1] === fileURLToPath(import.meta.url)) await main();
