# Passport — IF-BS-22F-F8C31I

## Object

Atomic encrypted-file custody preflight for a persistent Ed25519 identity root.

## Closed

- Lean formalizes outside-workspace, encryption, POSIX modes, passphrase separation, no-overwrite and recovery requirements.
- Workspace and relative destinations are rejected before writing.
- Weak and mismatched passphrases are rejected.
- Test keys are encrypted PKCS#8 with `0700/0600` permissions.
- Public receipt contains the root fingerprint and no passphrase.
- Existing custody directories are never overwritten.
- Wrong-passphrase inspection fails closed.

## Not executed

- No operational root key was generated.
- No author passphrase was requested, inferred or stored.
- No recovery copy was created or verified.
- No external fingerprint publication occurred.

## Decision gate

Confirm encrypted offline-file custody and choose the absolute destination outside `/Users/test/Documents/Codex`. The passphrase must be entered by the author during the local ceremony and must not be sent through chat.

## Next point

F8C31J: execute the offline ceremony with author-supplied local passphrase, verify one separately stored recovery copy, and export only the public key and witness candidate.
