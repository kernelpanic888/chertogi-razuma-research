# Passport — IF-BS-22F-F8C31G

## Object

Two-release trust-continuity fixture with an identity-root anchor, three-party rotation, explicit old-key revocation and an external fingerprint input.

## Closed

- Lean defines trusted state, accepted rotation, key revocation and release trust.
- Lean proves activation of the new key, rejection of the old key and trust of the next correctly signed release.
- Root, old and new keys all sign the same canonical rotation digest.
- Release 2 links both the previous release and the accepted rotation.
- Release 2 addresses a five-artifact canonical content manifest; artifact corruption fails content while key continuity remains valid.
- A valid old-key signature after revocation is rejected by policy.
- A wrong external fingerprint does not damage content or chain verification; it only prevents author recognition.
- No private key is retained.

## Not claimed

- The generated fixture keys are not operational author keys.
- The root fingerprint is not yet independently published.
- The local `anchor-fingerprint.txt` is a publication candidate, not an external witness.
- Signature security remains a trusted runtime primitive.

## Next point

F8C31H: perform an operational key ceremony outside the repository, publish the root fingerprint through an author-controlled external channel, and verify the public witness without adding a network dependency to the research page.
