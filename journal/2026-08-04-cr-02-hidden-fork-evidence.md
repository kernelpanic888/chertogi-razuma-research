# CR-02 · When a hidden fork becomes evidence

**Date:** 2026-08-04<br>
**Status:** working research model<br>
**Author:** Salkutsan Aleksey Anatolievich

![CR-02: witness field and hidden-fork discovery](assets/2026-08-04-cr-02-witness-field.png)

## Reading

A private fork becomes evidence only when two incompatible, signed views of one slot meet.

While witness A sees only head `51α` and witness B sees only `51β`, each locally observes an admissible continuation. Once gossip connects them, the pair becomes compact and verifiable: one identity, one slot and one parent, but two different signed heads.

```text
Wₙ = (id, n, parentHead, head, σ)

Fork(Wᵃ, Wᵇ) ⇔
  sameSlot(Wᵃ, Wᵇ) ∧ headᵃ ≠ headᵇ
```

Gossip does not choose the true branch. It proves the narrower claim that one continuous history is no longer compatible with all received evidence.

This is neither a new cipher nor a proof of global discovery in a permanently partitioned network. The model requires at least one honest witness to observe each branch and eventual reconnection between witnesses.

## Canonical artifacts

- [Live CR-01/CR-02 reader](https://chertogi-razuma-research.kernelpanic888.chatgpt.site/readers/certified-continuity-protocol/#cr02-map)
- [Exact visual source at commit `bb05467`](https://github.com/kernelpanic888/chertogi-razuma-research/blob/bb05467dca70ea010d97f9d73faf89b828d99faf/public/readers/certified-continuity-protocol/index.html)
- [Protocol, Lean and reference implementation repository](https://github.com/kernelpanic888/Salkutsan-Certified-Continuity-Protocol)
- [Release `sccp-v0.1.0`](https://github.com/kernelpanic888/Salkutsan-Certified-Continuity-Protocol/releases/tag/sccp-v0.1.0)

## Formal boundary

CR-01 already contains a checked formal kernel and reference implementation in its dedicated repository. The CR-02 witness/gossip condition shown here is a visual working model and has not yet been closed as a Lean theorem.

## Next passport step

Freeze the mutation matrix and the honest-witness/eventual-connectivity assumptions before implementing executable gossip or claiming global fork detection.
