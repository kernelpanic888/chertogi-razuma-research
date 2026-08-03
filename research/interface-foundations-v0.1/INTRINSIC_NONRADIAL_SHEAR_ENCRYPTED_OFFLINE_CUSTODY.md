# IF-BS-22F-F8C31I — Encrypted offline custody preflight

## Safety predicate

`SafeCustody := outside(release) ∧ encrypted ∧ mode(dir)=0700 ∧ mode(key)=0600 ∧ passphrase_separate ∧ no_overwrite ∧ recovery_verified`

The persistent identity root is a secret with a different boundary from public proof artifacts. It must have no path into the repository, public reader, manifest, witness or deployment archive.

## Prepared implementation

The preflight/generator:

1. requires an absolute destination outside the workspace;
2. resolves existing ancestors to detect symlinked workspace paths;
3. requires a confirmed passphrase of at least 24 characters;
4. exports Ed25519 only as AES-256-CBC encrypted PKCS#8;
5. stages files in a fresh `0700` directory and atomically renames it;
6. writes the private key as `0600` and refuses every overwrite;
7. writes a public receipt containing only the fingerprint and custody facts;
8. can decrypt and compare public fingerprints during inspection without printing the key or passphrase.

## Honest boundary

Only temporary test keys were generated. The operational root has not been created because the custody choice and passphrase belong to the author, not to the public research process. The current CLI supports environment-supplied passphrases for eventual execution; the values are never logged or stored in receipts, but operational use still requires a deliberate local ceremony.

## Русское чтение

Секретный корень не является частью доказательства и не должен попасть в его границу. Безопасная геометрия здесь проста: проект и сайт лежат по одну сторону, зашифрованный ключ — в отдельном офлайн-хранилище, а наружу возвращается только отпечаток открытого ключа.
