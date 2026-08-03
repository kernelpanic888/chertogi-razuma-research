import IntrinsicNonradialShearFiniteSaturation

namespace BoundaryOfSelf.IntrinsicNonradialShearFiniteSaturationAudit

open scoped Topology
open Set Filter
open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearTangentEnvelope
open IntrinsicNonradialShearFiniteSaturation

theorem audited_finite_saturation_pair
    {X Y : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hunit : X ^ 2 + Y ^ 2 = 1) (index : ℕ) :
    saturationFirstPoint X Y index ∈ directionalDiamondBand ∧
      saturationSecondPoint X Y index ∈ directionalDiamondBand :=
  ⟨saturationFirstPoint_mem hX0 hY0 hunit index,
    saturationSecondPoint_mem hX0 hY0 hunit index⟩

theorem audited_pair_distance
    {X Y : ℝ} (hunit : X ^ 2 + Y ^ 2 = 1) (index : ℕ) :
    dist (saturationFirstPoint X Y index)
        (saturationSecondPoint X Y index) =
      2 * saturationScale index :=
  saturation_pair_dist hunit index

theorem audited_finite_difference
    {amplitude X Y : ℝ} (ha0 : 0 ≤ amplitude)
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hunit : X ^ 2 + Y ^ 2 = 1) (index : ℕ) :
    |forwardBlowUpSq amplitude (saturationFirstPoint X Y index) -
        forwardBlowUpSq amplitude (saturationSecondPoint X Y index)| =
      saturationApproximation amplitude X Y index *
        (2 * saturationScale index) :=
  saturation_forward_difference ha0 hX0 hY0 hunit index

theorem audited_quotient_limit (amplitude X Y : ℝ) :
    Tendsto (saturationApproximation amplitude X Y) atTop
      (𝓝 (2 * amplitude * (Y + (X + amplitude) * (X + Y)))) :=
  saturationApproximation_tendsto amplitude X Y

theorem audited_exact_global_least
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    IsLeast (GlobalDiamondChordModuli amplitude)
      (exactLocalTangentModulus amplitude) :=
  exactLocalTangentModulus_isLeast_global ha0

#print axioms audited_finite_saturation_pair
#print axioms audited_pair_distance
#print axioms audited_finite_difference
#print axioms audited_quotient_limit
#print axioms audited_exact_global_least

end BoundaryOfSelf.IntrinsicNonradialShearFiniteSaturationAudit
