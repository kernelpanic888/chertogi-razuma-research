import Std

namespace P1OptionalAggregateStore

inductive Route where
  | publicReader
  | analytics
deriving Repr, DecidableEq

def routeMounted (store : Option Unit) (route : Route) : Bool :=
  match route with
  | .publicReader => true
  | .analytics => store.isSome

theorem no_store_means_no_analytics : routeMounted none .analytics = false := by
  rfl

theorem public_reader_survives_without_store : routeMounted none .publicReader = true := by
  rfl

def atomicBatch (dailyBudget used arrivals : Nat) : Nat :=
  min dailyBudget (used + arrivals)

theorem atomic_batch_is_bounded (dailyBudget used arrivals : Nat) :
    atomicBatch dailyBudget used arrivals <= dailyBudget := by
  exact Nat.min_le_left _ _

theorem zero_arrivals_preserve_bounded_state
    (dailyBudget used : Nat) (bounded : used <= dailyBudget) :
    atomicBatch dailyBudget used 0 = used := by
  simp [atomicBatch, Nat.min_eq_right bounded]

end P1OptionalAggregateStore

#print axioms P1OptionalAggregateStore.no_store_means_no_analytics
#print axioms P1OptionalAggregateStore.public_reader_survives_without_store
#print axioms P1OptionalAggregateStore.atomic_batch_is_bounded
#print axioms P1OptionalAggregateStore.zero_arrivals_preserve_bounded_state
