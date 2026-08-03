# CR-03 · Physical continuity anchor

**Date:** 2026-08-04  
**Status:** executable provider contract and working physical model  
**Author:** Salkutsan Aleksey Anatolievich

## Reading

The next protection layer is not a blockchain and not a new cipher. It binds an accepted continuity head to a physical anchor expected to protect a signing key, monotonic epoch and measured environment.

`P_n = (anchorId, id, n, parentHead, stateHead, H(measurements), H(challenge))`

`R_n = (P_n, measurements, Sign(sk_anchor, domain || canonical(P_n)))`

The executable contract accepts only the exact next protected epoch, pinned identity and expected parent/state heads. A fresh verifier challenge prevents a saved receipt from answering a new session. Independent witnesses compare compact receipts rather than private state.

Two valid receipts from one pinned anchor with the same identity, epoch and parent but different state heads are evidence of equivocation or anchor cloning under the assumptions. They do not identify the true branch.

## Canonical artifacts

- [Live CR-03 physical map](https://chertogi-razuma-research.kernelpanic888.chatgpt.site/readers/certified-continuity-protocol/#cr03-physical-anchor)
- [Reference provider code](https://github.com/kernelpanic888/Salkutsan-Certified-Continuity-Protocol/blob/4498e361929ecf78342303877469caa2e82153f2/src/physical-anchor.mjs)
- [Physical anchor passport](https://github.com/kernelpanic888/Salkutsan-Certified-Continuity-Protocol/blob/4498e361929ecf78342303877469caa2e82153f2/docs/PHYSICAL_ANCHOR.md)
- [IETF RATS Architecture, RFC 9334](https://www.rfc-editor.org/rfc/rfc9334.html)
- [Remote Integrity Verification with TPMs, RFC 9683](https://www.rfc-editor.org/rfc/rfc9683.html)
- [Trusted Computing Group TPM specifications](https://trustedcomputinggroup.org/work-groups/trusted-platform-module/)

## Boundary

Lean records a consequence of the anchored-successor relation. It does not prove a particular TPM, counter, measurement root or provisioning ceremony physically honest. The included provider is a software simulator.

## Next passport step

Implement one real TPM-class provider and run the frozen attack matrix: rollback, replay, measured-state change, partition and witness reconnection.
