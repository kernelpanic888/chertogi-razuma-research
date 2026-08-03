import AggregateCounter

namespace P1CounterObservability

open P1AggregateCounter

/-- The model never contains the token itself, only the result of its check. -/
inductive ReadActor where
  | anonymous
  | owner
deriving Repr, DecidableEq

structure ReadCredential where
  actor : ReadActor
  bearerValid : Bool
deriving Repr, DecidableEq

def publicCredential : ReadCredential :=
  { actor := .anonymous, bearerValid := false }

def ownerCredential : ReadCredential :=
  { actor := .owner, bearerValid := true }

def invalidOwnerCredential : ReadCredential :=
  { actor := .owner, bearerValid := false }

def authorized (credential : ReadCredential) : Bool :=
  credential.actor == .owner && credential.bearerValid

/-- One accepted page view changes exactly one aggregate field by exactly one. -/
def acceptPageView (state : Counts) : Counts :=
  { state with pageView := state.pageView + 1 }

/-- Reading returns a value only to an authenticated owner and never changes state. -/
def readPageViews (state : Counts) (credential : ReadCredential) :
    Counts × Option Nat :=
  (state, if authorized credential then some state.pageView else none)

def OwnerObservable : Prop :=
  forall state : Counts,
    (readPageViews (acceptPageView state) ownerCredential).2 =
      some (state.pageView + 1)

def PublicHidden : Prop :=
  forall state : Counts,
    (readPageViews state publicCredential).2 = none

theorem accepted_view_is_exact (state : Counts) :
    (acceptPageView state).pageView = state.pageView + 1 := by
  rfl

theorem accepted_view_preserves_other_counts (state : Counts) :
    (acceptPageView state).readerOpen = state.readerOpen ∧
    (acceptPageView state).languageSwitch = state.languageSwitch ∧
    (acceptPageView state).supportOpen = state.supportOpen := by
  exact ⟨rfl, rfl, rfl⟩

theorem read_is_state_preserving (state : Counts) (credential : ReadCredential) :
    (readPageViews state credential).1 = state := by
  rfl

theorem owner_reads_exact_state (state : Counts) :
    (readPageViews state ownerCredential).2 = some state.pageView := by
  rfl

theorem public_reads_nothing (state : Counts) :
    (readPageViews state publicCredential).2 = none := by
  rfl

theorem invalid_owner_reads_nothing (state : Counts) :
    (readPageViews state invalidOwnerCredential).2 = none := by
  rfl

theorem owner_observability_contract : OwnerObservable := by
  intro state
  rfl

theorem public_non_disclosure_contract : PublicHidden := by
  intro state
  rfl

theorem accepted_view_then_owner_read (state : Counts) :
    (readPageViews (acceptPageView state) ownerCredential).2 =
      some (state.pageView + 1) := by
  rfl

theorem accepted_view_then_public_read_is_hidden (state : Counts) :
    (readPageViews (acceptPageView state) publicCredential).2 = none := by
  rfl

end P1CounterObservability

#print axioms P1CounterObservability.accepted_view_is_exact
#print axioms P1CounterObservability.read_is_state_preserving
#print axioms P1CounterObservability.owner_observability_contract
#print axioms P1CounterObservability.public_non_disclosure_contract
#print axioms P1CounterObservability.accepted_view_then_owner_read
