# Passport — IF-BS-22F-F8C31F

## Object

Content-addressed capsule for the F8C31E canonical replay release, with a cryptographic provenance attestation kept logically separate from content verification.

## Closed

- Canonical manifest lists nine exact artifacts by relative path, byte count and SHA-256 digest.
- Manifest bytes have their own SHA-256 address.
- Ed25519 signature is checked over that manifest digest.
- Public-key identifier is recomputed from SPKI bytes.
- F8C31E replay remains part of the content gate.
- Lean proves the separation law and conjunction gate without modelling cryptographic internals.
- Blind tests separately corrupt one artifact and the signature.

## Not claimed

- SHA-256 collision resistance and Ed25519 security are trusted runtime primitives, not Lean theorems in this slice.
- A valid signature does not prove mathematical truth.
- The embedded public key is not yet independently bound to Aleksey Salkutsan's identity.
- The one-time private release key was not stored in the repository.

## Next point

F8C31G: define an external identity-anchor record and a rotation/revocation chain, then test continuity of trust across two signed releases without making identity part of mathematical content acceptance.
