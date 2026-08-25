/-!
AMF-02 / Adaptive Market Hypothesis Steward

A small, self-contained Lean carrier for the operational structure displayed by
the reader.  It formalizes a finite action selector for a hypothesis card.  It
does not formalize a market, price formation, profitability, or calibration.
-/

namespace AMF02

inductive Phase where
  | open
  | confirmed
  | invalidated
  | expired
  | archived
  deriving DecidableEq, Repr

inductive Action where
  | awaitNext
  | refreshData
  | verify
  | callModel
  | close
  | archive
  deriving DecidableEq, Repr

structure Card where
  identity : Nat
  phase : Phase
  freshness : Nat
  support : Nat
  counterevidence : Nat
  noise : Nat
  timeLeft : Nat
  attention : Nat
  compute : Nat
  traceLength : Nat
  deriving Repr

def terminal : Phase → Bool
  | .invalidated | .expired | .archived => true
  | .open | .confirmed => false

def mustClose (c : Card) : Bool :=
  c.timeLeft == 0 || decide (80 ≤ c.counterevidence)

def stale (c : Card) : Bool := decide (c.freshness < 60)

def verifyNeeded (c : Card) : Bool :=
  (decide (55 ≤ c.noise) ||
    (decide (45 ≤ c.support) && decide (45 ≤ c.counterevidence))) &&
  decide (0 < c.attention)

def eventful (c : Card) : Bool :=
  decide (70 ≤ c.support) || decide (70 ≤ c.counterevidence)

def hasCompute (c : Card) : Bool := decide (0 < c.compute)

/- The fixed admissibility contract. Ranking is deliberately absent here. -/
def admissible (c : Card) : Action → Bool
  | .archive => terminal c.phase
  | .close => !terminal c.phase && mustClose c
  | .refreshData => !terminal c.phase && !mustClose c && stale c
  | .verify =>
      !terminal c.phase && !mustClose c && !stale c && verifyNeeded c
  | .callModel =>
      !terminal c.phase && !mustClose c && !stale c && !verifyNeeded c &&
        eventful c && hasCompute c
  | .awaitNext =>
      !terminal c.phase && !mustClose c && !stale c && !verifyNeeded c &&
        !(eventful c && hasCompute c)

/- The selector ranks only after the admissibility conditions are known. -/
def choose (c : Card) : Action :=
  if terminal c.phase then .archive
  else if mustClose c then .close
  else if stale c then .refreshData
  else if verifyNeeded c then .verify
  else if eventful c && hasCompute c then .callModel
  else .awaitNext

def allActions : List Action :=
  [.awaitNext, .refreshData, .verify, .callModel, .close, .archive]

def goalField (c : Card) : List Action :=
  allActions.filter (admissible c)

theorem choose_is_admissible (c : Card) : admissible c (choose c) = true := by
  cases hT : terminal c.phase <;>
  cases hC : mustClose c <;>
  cases hS : stale c <;>
  cases hV : verifyNeeded c <;>
  cases hE : eventful c <;>
  cases hB : hasCompute c <;>
  simp [choose, admissible, hT, hC, hS, hV, hE, hB]

theorem choose_mem_goalField (c : Card) : choose c ∈ goalField c := by
  apply List.mem_filter.mpr
  constructor
  · cases choose c <;> simp [allActions]
  · exact choose_is_admissible c

theorem terminal_selects_archive (c : Card)
    (h : terminal c.phase = true) : choose c = .archive := by
  simp [choose, h]

theorem mustClose_precedes_review (c : Card)
    (hT : terminal c.phase = false) (hC : mustClose c = true) :
    choose c = .close := by
  simp [choose, hT, hC]

theorem stale_precedes_review (c : Card)
    (hT : terminal c.phase = false) (hC : mustClose c = false)
    (hS : stale c = true) : choose c = .refreshData := by
  simp [choose, hT, hC, hS]

theorem callModel_requires_gate (c : Card) (h : choose c = .callModel) :
    stale c = false ∧ eventful c = true ∧ hasCompute c = true := by
  cases hT : terminal c.phase <;>
  cases hC : mustClose c <;>
  cases hS : stale c <;>
  cases hV : verifyNeeded c <;>
  cases hE : eventful c <;>
  cases hB : hasCompute c <;>
  simp [choose, hT, hC, hS, hV, hE, hB] at h ⊢

def applyAction (c : Card) : Action → Card
  | .awaitNext =>
      { c with timeLeft := c.timeLeft - 1, traceLength := c.traceLength + 1 }
  | .refreshData =>
      { c with freshness := 100, traceLength := c.traceLength + 1 }
  | .verify =>
      { c with attention := c.attention - 1, traceLength := c.traceLength + 1 }
  | .callModel =>
      { c with compute := c.compute - 1, traceLength := c.traceLength + 1 }
  | .close =>
      { c with
        phase := if c.timeLeft == 0 then .expired else .invalidated
        traceLength := c.traceLength + 1 }
  | .archive =>
      { c with phase := .archived, traceLength := c.traceLength + 1 }

theorem apply_preserves_identity (c : Card) (a : Action) :
    (applyAction c a).identity = c.identity := by
  cases a <;> rfl

theorem apply_extends_trace (c : Card) (a : Action) :
    (applyAction c a).traceLength = c.traceLength + 1 := by
  cases a <;> rfl

theorem await_preserves_compute (c : Card) :
    (applyAction c .awaitNext).compute = c.compute := by
  rfl

theorem callModel_consumes_one_compute (c : Card) :
    (applyAction c .callModel).compute = c.compute - 1 := by
  rfl

theorem close_is_terminal (c : Card) :
    terminal (applyAction c .close).phase = true := by
  by_cases h : c.timeLeft = 0
  · simp [applyAction, h, terminal]
  · simp [applyAction, h, terminal]

theorem closed_card_cannot_reopen (c : Card) :
    choose (applyAction c .close) = .archive := by
  apply terminal_selects_archive
  exact close_is_terminal c

theorem archive_is_absorbing (c : Card) :
    choose (applyAction c .archive) = .archive := by
  apply terminal_selects_archive
  rfl

#print axioms choose_is_admissible
#print axioms choose_mem_goalField
#print axioms callModel_requires_gate
#print axioms apply_preserves_identity
#print axioms closed_card_cannot_reopen
#print axioms archive_is_absorbing

end AMF02
