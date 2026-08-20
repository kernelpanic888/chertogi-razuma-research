# CSS-02 · Quarantine refinement

**2026-08-04 · verified local slice · 9/9 blind scenes**

The Certified System Steward no longer deletes through the public cache name. The macOS provider opens the admitted identity, moves it with `RENAME_EXCL` into a private `0700` quarantine and removes it relative to held directory descriptors.

```text
named target = d -> exclusive quarantine(d) -> erase(fd(d)) -> original name absent
```

If the original name reappears, the replacement is preserved and the transition is rejected. This directly narrows the check/use race described by [MITRE CWE-367](https://cwe.mitre.org/data/definitions/367.html); exclusive rename relies on the filesystem capability documented by [Apple](https://developer.apple.com/documentation/foundation/urlresourcevalues/volumesupportsexclusiverenaming).

**Verified:** runtime `9/9`; Lean audit unchanged at seven theorems without extra axioms; real preview performed no deletion and created no audit epoch.

**Red boundary:** a malicious concurrent process with the same uid remains outside the proved model. Production status still requires privilege separation or an OS delete-by-handle capability and independent review.

[Reader map](../public/readers/certified-continuity-protocol/index.html#css02-steward) · [Provider](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/platform/macos-safe-remove.c) · [AR-02](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/CERTIFIED_SYSTEM_STEWARD_ADVERSARIAL_REVIEW.md) · [Tests](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/tests/certified-system-steward.test.mjs)

