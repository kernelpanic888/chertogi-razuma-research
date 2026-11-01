import ER01.Core
set_option autoImplicit false
namespace ER01.Instrument

/-- Integer effect weights for K_s=diag(1,lambda),
    K_f=diag(0,sqrt(1-lambda^2)). This module proves the diagonal
    probability identities; it does not formalize complex Kraus matrices. -/
def failureMass (c : Config) : Nat :=
  (c.d ^ 2 - c.l ^ 2) * (c.q - c.p)

def outcomeMasses (c : Config) : List Nat :=
  [(weights c).zero, (weights c).one, 0, failureMass c]

theorem success_agrees_with_core (c : Config) :
    (weights c).zero + (weights c).one = (weights c).total := rfl

theorem instrument_complete (c : Config) :
    (weights c).total + failureMass c = commonDenominator c := by
  have hsq : c.l ^ 2 ≤ c.d ^ 2 := Nat.pow_le_pow_left c.l_le 2
  have hp : c.p + (c.q - c.p) = c.q := Nat.add_sub_of_le c.p_le
  unfold weights Mass.total failureMass commonDenominator
  calc
    c.p * c.d ^ 2 + c.l ^ 2 * (c.q - c.p) +
        (c.d ^ 2 - c.l ^ 2) * (c.q - c.p)
      = c.p * c.d ^ 2 +
          (c.l ^ 2 + (c.d ^ 2 - c.l ^ 2)) * (c.q - c.p) := by
            rw [Nat.add_mul, Nat.add_assoc]
    _ = c.p * c.d ^ 2 + c.d ^ 2 * (c.q - c.p) := by
      rw [Nat.add_sub_of_le hsq]
    _ = (c.p + (c.q - c.p)) * c.d ^ 2 := by
      rw [Nat.add_mul, Nat.mul_comm (c.q - c.p)]
    _ = c.q * c.d ^ 2 := by rw [hp]

theorem all_outcomes_complete (c : Config) :
    (outcomeMasses c).sum = commonDenominator c := by
  simpa [outcomeMasses, Mass.total, Nat.add_assoc] using instrument_complete c

theorem failure_bounded (c : Config) : failureMass c ≤ commonDenominator c := by
  have h := instrument_complete c
  omega

theorem transparent_filter_never_fails (c : Config) (h : c.l = c.d) :
    failureMass c = 0 := by simp [failureMass, h]

theorem pure_zero_never_fails (c : Config) (h : c.p = c.q) :
    failureMass c = 0 := by simp [failureMass, h]

theorem blocked_pure_one_has_no_posterior
    (c : Config) (hp : c.p = 0) (hl : c.l = 0) :
    posterior (weights c) = none := by
  apply (posterior_none_iff _).mpr
  simp [weights, Mass.total, hp, hl]

end ER01.Instrument
