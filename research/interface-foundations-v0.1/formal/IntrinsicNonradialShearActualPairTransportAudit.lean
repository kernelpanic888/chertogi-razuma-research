import IntrinsicNonradialShearActualPairTransport

namespace BoundaryOfSelf.IntrinsicNonradialShearActualPairTransportAudit

open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearTangentEnvelope
open IntrinsicNonradialShearActualPairTransport

theorem audited_parallelogram_width (m h : ℝ) :
    |m + h| + |m - h| = 2 * max |m| |h| :=
  abs_add_abs_sub_eq_two_max m h

theorem audited_centered_record
    {x₁ y₁ x₂ y₂ : ℝ}
    (hfirst : x₁ ^ 2 + y₁ ^ 2 = 1)
    (hsecond : x₂ ^ 2 + y₂ ^ 2 = 1) :
    ∃ X Y r k : ℝ,
      0 ≤ X ∧ 0 ≤ Y ∧ 0 ≤ r ∧ 0 ≤ k ∧
      X ^ 2 + Y ^ 2 = 1 ∧ r ^ 2 + k ^ 2 = 1 ∧
      r ^ 2 = ((x₁ + x₂) / 2) ^ 2 + ((y₁ + y₂) / 2) ^ 2 ∧
      k ^ 2 = ((x₁ - x₂) / 2) ^ 2 + ((y₁ - y₂) / 2) ^ 2 ∧
      |(x₁ + x₂) / 2| = r * X ∧
      |(y₁ + y₂) / 2| = r * Y ∧
      |(x₁ - x₂) / 2| = k * Y ∧
      |(y₁ - y₂) / 2| = k * X :=
  exists_centered_record_of_unit_pair hfirst hsecond

theorem audited_actual_pair_global_upper
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude)
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand) :
    |forwardBlowUpSq amplitude first -
        forwardBlowUpSq amplitude second| ≤
      exactLocalTangentModulus amplitude * dist first second :=
  forwardBlowUpSq_actual_pair_exact_bound ha0 hfirst hsecond

#print axioms audited_parallelogram_width
#print axioms audited_centered_record
#print axioms audited_actual_pair_global_upper

end BoundaryOfSelf.IntrinsicNonradialShearActualPairTransportAudit

