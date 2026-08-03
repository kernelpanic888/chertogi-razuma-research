import Std

namespace P1AnonymousAdmission

structure ObservableRequest where
  method : String
  route : String
  bodyBytes : Nat
deriving Repr, DecidableEq

inductive HiddenActor where
  | human
  | bot
deriving Repr, DecidableEq

structure OriginatedRequest where
  observable : ObservableRequest
  actor : HiddenActor
deriving Repr, DecidableEq

abbrev AdmissionPolicy := ObservableRequest -> Bool

def decide (policy : AdmissionPolicy) (request : OriginatedRequest) : Bool :=
  policy request.observable

theorem actor_indistinguishability
    (policy : AdmissionPolicy) (observable : ObservableRequest)
    (left right : HiddenActor) :
    decide policy { observable := observable, actor := left } =
      decide policy { observable := observable, actor := right } := by
  rfl

def admittedWork (dailyBudget emitted : Nat) : Nat := min dailyBudget emitted

theorem admitted_work_is_globally_bounded (dailyBudget emitted : Nat) :
    admittedWork dailyBudget emitted <= dailyBudget := by
  exact Nat.min_le_left _ _

theorem accepted_increment_respects_budget
    (dailyBudget used : Nat) (admitted : used < dailyBudget) :
    used + 1 <= dailyBudget := by
  exact admitted

end P1AnonymousAdmission

#print axioms P1AnonymousAdmission.actor_indistinguishability
#print axioms P1AnonymousAdmission.admitted_work_is_globally_bounded
#print axioms P1AnonymousAdmission.accepted_increment_respects_budget
