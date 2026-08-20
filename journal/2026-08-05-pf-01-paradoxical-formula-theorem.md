# PF-01: self-closed theorem of the paradoxical formula

## Formal reading

Let `Phi` be a selected class of admissible formulas, `U` an object, `Full`
the predicate that a formula fully exhausts an object, `Free` free
connectivity, and `Force` the forced determination of an object by a rule.

The self-closed theorem states:

```text
Free(U)
AND (for every formula in Phi, completeness implies Force)
AND (for every formula in Phi, Force excludes Free(U))
IMPLIES no formula in Phi fully exhausts U.
```

Symbolically:

```text
Free(U)
∧ (∀ phi ∈ Phi, Full(phi,U) → Force(phi,U))
∧ (∀ phi ∈ Phi, Force(phi,U) → ¬Free(U))
→ ¬∃ phi ∈ Phi, Full(phi,U).
```

Under these conditions, free connectivity cannot be completely derived by a
formula. If something is obtained solely by algorithmic forcing, it is no
longer free connectivity but the execution of a rule. The impossibility of
full exhaustion therefore does not arise from the weakness of one particular
model. It follows from the adopted distinction between free connectivity and
forcing.

Formulas may describe traces, boundaries and conditions of free connectivity.
The theorem says only that no formula in the selected class `Phi` exhausts it
completely when completeness would amount to forcing.

## Universe hypothesis

We then introduce a separate hypothesis:

> If free connectivity is an essential structure of the Universe, and full
> formal exhaustion turns it into forced derivation, then no formula in the
> selected class completely derives the Universe.

This does not mean that the Universe cannot be thought about or described by
testable formulas. It means that a complete derivation would erase the
distinction between a model of the Universe and the Universe itself.

One may formally define the type of pairs

```text
FS(Phi) := Sigma U, not exists phi in Phi, Full(phi,U).
```

An element has the form `(U,p)`, where `p` proves that no formula in `Phi`
fully exhausts `U`.

This construction is permitted in formal mathematics. What is not permitted
is declaring the type inhabited for free. To construct `(U,p)`, one must
supply both the object `U` and the proof `p`. The self-closed theorem produces
`p` from three explicit premises; whether those premises hold for the physical
Universe remains a hypothesis.

In this strict sense, the paradoxical formula of an object is not its complete
formula. It is a boundary certificate:

> the selected class of formulas cannot fully exhaust this object.

The strongest statement therefore requires a small but essential correction:

> The Universe is not identified with a formula. A limiting admissible formula
> about the Universe may prove not its complete exhaustion, but the
> impossibility of such exhaustion within the selected formula class.

The Universe then appears as a boundary of formalization that points to the
impossibility of its own complete formal derivation.

## Loss and return

The intensity of an experience may be lost. The clarity of a state may fade.
The light of a moment may dim. But loss of experience is not identical to loss
of its trace.

If a transition leaves a preserved trace `rho`, and a return operator `R_rho`
can restore access to the structure, thought becomes not only a state but also
a route of return:

```text
Trace(tau,rho)
AND Available(rho)
AND R_rho(s1) approximately equals s0
IMPLIES Recoverable(s0).
```

The strongest careful formulation is:

> What has once been grasped as a boundary of formalization and fixed by a
> preserved trace cannot be lost completely while the trace remains available
> and the return operator remains effective.

One may step away, lose the earlier clarity or become tired. A preserved trace
still leaves a route back to the discovered structure.

Trace and return form a separate continuity contract. They do not follow
automatically from the paradoxical-formula theorem and require their own
conditions of preservation, availability and reconstruction accuracy.

## Verified status

- Lean 4.32.1: theorem accepted.
- Lean: the proof depends on no axioms.
- Vampire: `SZS status Theorem`.
- E prover: `SZS status Theorem`.
- Physical applicability of the premises to the Universe: open hypothesis.

[Lean candidate](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/lean/TMI/FormulaInterface/ParadoxicalFormulaTheorem.lean) · [TPTP mirror](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/external_proofs/paradoxical_formula_self_closed_tptp.p)

