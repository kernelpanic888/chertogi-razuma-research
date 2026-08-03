# Passport — IF-BS-22F-F8C31H

## Object

Public-only offline ceremony tool and formal witness predicate for an operational identity root.

## Closed

- Lean requires matching subject, matching root observation and independent source.
- Lean rejects self-witness and a mismatched observed fingerprint.
- The tool derives SHA-256 from SPKI public-key bytes.
- The tool emits canonical witness JSON without secret material or network access.
- The tool rejects the research site's own host and all private-key input.
- Blind tests use temporary in-memory keys only.

## Not executed

- No persistent operational root key exists.
- No encrypted-file or hardware-token custody method has been selected.
- No fingerprint has been externally published.
- No real external witness has been observed.

## Decision gate

Choose operational key custody: encrypted offline file or hardware-backed key. Then generate the root outside the repository, publish only its fingerprint through an author-controlled channel, and verify a separately saved witness copy.

## Next point

F8C31I: execute the selected key ceremony and bind the independently observed root fingerprint to the existing trust-chain protocol.
