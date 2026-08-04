# CSS-01 · Certified System Steward

**2026-08-04 · verified local slice · macOS refinement**

The formal model is now connected to a functional system program without allowing the shell layer to invent policy.

## Contract

```text
Lean specification -> passport -> platform adapter -> runtime receipt

AdmittedTransition =
  action in field
  and apply(before, action) = after
  and policy admits(before, action, after)
  and protected(after) = protected(before)
```

The Lean audit reports no extra axioms for the seven inspected theorems. The runtime blind suite passes seven scenarios: ordinary cleanup, foreign path, target symlink, internal symlink, changed field, protected-file mutation and contradictory receipt views.

## macOS refinement

The executor uses a small protected C provider built around directory file descriptors, `openat`, `fstatat` and `unlinkat`. It never follows an admitted cache symlink and keeps policy, action field and protected projection in the signed passport.

This addresses the ordinary check/use gap described by [MITRE CWE-367](https://cwe.mitre.org/data/definitions/367.html) and follows the descriptor-relative semantics documented for macOS [`unlinkat`](https://manp.gs/mac/2/unlink), [`fstatat`](https://manp.gs/mac/2/stat) and [symbolic links](https://manp.gs/mac/7/symlink).

## Red boundary

This is a verified research slice, not a claim of complete production hardening. A residual final-name race remains until the target is first moved into an owned quarantine directory or the platform exposes an equivalent delete capability bound to the already verified object.

## Canonical artifacts

- [Formal model](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/CertifiedSystemSteward.lean)
- [Runtime](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/certified-system-steward.mjs)
- [macOS provider](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/platform/macos-safe-remove.c)
- [Adversarial review](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/CERTIFIED_SYSTEM_STEWARD_ADVERSARIAL_REVIEW.md)
- [Tests](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/tests/certified-system-steward.test.mjs)

