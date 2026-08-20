# CSS-03 / Authority cannot certify itself

Date: 2026-08-04  
Status: formal contract and adversarial protocol tests; physical helper not installed.

CSS-02 closes the ordinary public-name race by moving the exact opened object
into an exclusive quarantine before deletion. One red boundary remained: a
malicious process with the same user identity still has the same filesystem
authority as the executor.

CSS-03 records why another same-user wrapper cannot close that boundary:

```text
W(helper, quarantine) and not W(client, quarantine)  ->  client != helper
```

The client selects a target and commits its identity, policy digest, protected
state, epoch and nonce. A separate helper observes and acts. The return receipt
binds the exact request to the result. Root identity and code identity are not
trusted when they appear inside the receipt payload; they must be supplied by
an authenticated operating-system channel.

## Evidence in this slice

- Lean 4 contract: distinct principals, protected-state preservation, exact
  request binding and rejection of source-name reappearance.
- Runtime-neutral protocol verifier.
- Nine blind scenarios covering valid admission, same-UID impersonation,
  unverified code identity, request mutation, object substitution, protected
  drift, source reappearance, policy substitution and replay.
- Result: 9/9 pass.

## Platform shoulders

- [Apple Service Management](https://developer.apple.com/documentation/servicemanagement/)
- [Apple: updating helper executables](https://developer.apple.com/documentation/servicemanagement/updating-helper-executables-from-earlier-versions-of-macos)
- [Apple XPC updates](https://developer.apple.com/documentation/updates/xpc)
- [Apple TN3127](https://developer.apple.com/documentation/technotes/tn3127-inside-code-signing-requirements)
- [MITRE CWE-362](https://cwe.mitre.org/data/definitions/362.html)

## Red boundary

No signed `SMAppService` LaunchDaemon has been installed. No physical XPC peer
has been authenticated. This is a checked protocol for the next implementation,
not a claim that same-UID isolation already exists. The operational system
therefore remains CSS-02.

Canonical artifacts: [TMI Lean Formal Library](https://github.com/kernelpanic888/TMI-Lean-Formal-Library) · [live reader](https://chertogi-razuma-research.kernelpanic888.chatgpt.site/readers/certified-continuity-protocol/)
