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

/-- Loading a local credential is distinct from validating it at the endpoint. -/
inductive CredentialLoad where
  | available (credential : ReadCredential)
  | unavailable
deriving Repr, DecidableEq

def authorized (credential : ReadCredential) : Bool :=
  credential.actor == .owner && credential.bearerValid

/-- One accepted page view changes exactly one aggregate field by exactly one. -/
def acceptPageView (state : Counts) : Counts :=
  { state with pageView := state.pageView + 1 }

/-- Reading returns a value only to an authenticated owner and never changes state. -/
def readPageViews (state : Counts) (credential : ReadCredential) :
    Counts × Option Nat :=
  (state, if authorized credential then some state.pageView else none)

/-- The database read and its delivery are different interfaces. -/
inductive TransportRead where
  | delivered (value : Nat)
  | empty
  | failed
deriving Repr, DecidableEq

inductive ObservedRead where
  | exact (value : Nat)
  | credentialUnavailable
  | unauthorized
  | malformed
  | transportFailure
deriving Repr, DecidableEq

/-- Transport classification is read-only even when delivery is absent. -/
def observePageViews (state : Counts) (credential : ReadCredential)
    (transport : TransportRead) : Counts × ObservedRead :=
  if authorized credential then
    match transport with
    | .delivered value =>
        if value == state.pageView then (state, .exact value)
        else (state, .malformed)
    | .empty => (state, .malformed)
    | .failed => (state, .transportFailure)
  else
    (state, .unauthorized)

/-- The complete read path begins before transport, at local credential loading. -/
def observeCounterRead (state : Counts) (credentialLoad : CredentialLoad)
    (transport : TransportRead) : Counts × ObservedRead :=
  match credentialLoad with
  | .available credential => observePageViews state credential transport
  | .unavailable => (state, .credentialUnavailable)

/-- A bounded retry keeps the first exact delivered value and skips failures. -/
def firstDelivered : List TransportRead → Option Nat
  | [] => none
  | .delivered value :: _ => some value
  | _ :: rest => firstDelivered rest

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

theorem observed_read_is_state_preserving
    (state : Counts) (credential : ReadCredential) (transport : TransportRead) :
    (observePageViews state credential transport).1 = state := by
  unfold observePageViews
  by_cases hAuth : authorized credential
  · rw [if_pos hAuth]
    cases transport with
    | delivered value =>
        change
          (if value == state.pageView then (state, ObservedRead.exact value)
            else (state, ObservedRead.malformed)).1 = state
        by_cases hValue : value == state.pageView
        · rw [if_pos hValue]
        · rw [if_neg hValue]
    | empty => rfl
    | failed => rfl
  · rw [if_neg hAuth]

theorem counter_read_is_state_preserving
    (state : Counts) (credentialLoad : CredentialLoad) (transport : TransportRead) :
    (observeCounterRead state credentialLoad transport).1 = state := by
  cases credentialLoad with
  | available credential =>
      exact observed_read_is_state_preserving state credential transport
  | unavailable => rfl

theorem unavailable_credential_is_explicit (state : Counts) (transport : TransportRead) :
    (observeCounterRead state .unavailable transport).2 = .credentialUnavailable := by
  rfl

theorem owner_observes_exact_canonical_delivery (state : Counts) :
    (observePageViews state ownerCredential (.delivered state.pageView)).2 =
      .exact state.pageView := by
  simp [observePageViews, authorized, ownerCredential]

theorem empty_delivery_is_malformed (state : Counts) :
    (observePageViews state ownerCredential .empty).2 = .malformed := by
  rfl

theorem failed_delivery_is_transport_failure (state : Counts) :
    (observePageViews state ownerCredential .failed).2 = .transportFailure := by
  rfl

theorem retry_skips_transport_failure (rest : List TransportRead) :
    firstDelivered (.failed :: rest) = firstDelivered rest := by
  rfl

theorem retry_skips_empty_delivery (rest : List TransportRead) :
    firstDelivered (.empty :: rest) = firstDelivered rest := by
  rfl

theorem retry_accepts_first_delivery (value : Nat) (rest : List TransportRead) :
    firstDelivered (.delivered value :: rest) = some value := by
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
#print axioms P1CounterObservability.observed_read_is_state_preserving
#print axioms P1CounterObservability.owner_observes_exact_canonical_delivery
#print axioms P1CounterObservability.retry_skips_transport_failure
#print axioms P1CounterObservability.retry_accepts_first_delivery
