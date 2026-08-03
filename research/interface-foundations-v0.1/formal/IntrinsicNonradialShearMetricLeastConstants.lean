import IntrinsicNonradialShearFiniteSaturation
import IntrinsicNonradialShearConditionChamber

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearMetricLeastConstants

noncomputable section

open IntrinsicNonradialShearKernelSharp
open IntrinsicNonradialShearSpectralMap
open IntrinsicNonradialShearSharpEnvelope

/-! ## IF-BS-22F-F8C27: least direct and inverse metric constants -/

def exactDirectMetricConstant (amplitude : ℝ) : ℝ :=
  Real.sqrt (exactDiamondUpperSq amplitude)

def exactInverseMetricConstant (amplitude : ℝ) : ℝ :=
  (Real.sqrt (exactDiamondLowerSq amplitude))⁻¹

def ForwardNonnegativeMetricModuli (amplitude : ℝ) : Set ℝ :=
  {constant | 0 ≤ constant ∧ ForwardMapMetricBound amplitude constant}

def BackwardNonnegativeMetricModuli (amplitude : ℝ) : Set ℝ :=
  {constant | 0 ≤ constant ∧ BackwardMapMetricBound amplitude constant}

theorem exactDiamondUpperSq_eq_forwardSpectralSq (amplitude : ℝ) :
    exactDiamondUpperSq amplitude = forwardSpectralSq amplitude := by
  unfold exactDiamondUpperSq forwardSpectralSq upperRadicand
  congr 2
  ring

theorem exactDiamondLowerSq_mul_inverseSpectralSq
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    exactDiamondLowerSq amplitude * inverseSpectralSq amplitude = 1 := by
  let A : ℝ := 1 - amplitude + amplitude ^ 2
  let R : ℝ := Real.sqrt (lowerRadicand amplitude)
  have hroot : R ^ 2 = lowerRadicand amplitude := by
    dsimp [R]
    exact lowerRoot_sq amplitude
  have hfactor :
      (A - amplitude * R) * (A + amplitude * R) =
        (1 - amplitude) ^ 2 := by
    calc
      (A - amplitude * R) * (A + amplitude * R) =
          A ^ 2 - amplitude ^ 2 * R ^ 2 := by ring
      _ = A ^ 2 - amplitude ^ 2 * lowerRadicand amplitude := by rw [hroot]
      _ = (1 - amplitude) ^ 2 := by
        dsimp [A]
        unfold lowerRadicand
        ring
  have hrad :
      lowerRadicand amplitude = amplitude ^ 2 - 2 * amplitude + 2 := by
    unfold lowerRadicand
    ring
  have hden : 1 - amplitude ≠ 0 := by linarith
  rw [inverseSpectralSq_closed_form ha1]
  rw [← hrad]
  change (A - amplitude * R) *
      ((A + amplitude * R) / (1 - amplitude) ^ 2) = 1
  calc
    (A - amplitude * R) *
        ((A + amplitude * R) / (1 - amplitude) ^ 2) =
      ((A - amplitude * R) * (A + amplitude * R)) /
        (1 - amplitude) ^ 2 := by ring
    _ = (1 - amplitude) ^ 2 / (1 - amplitude) ^ 2 := by rw [hfactor]
    _ = 1 := by field_simp [hden]

theorem inverseSpectralSq_eq_inv_exactDiamondLowerSq
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    inverseSpectralSq amplitude = (exactDiamondLowerSq amplitude)⁻¹ := by
  exact (inv_eq_of_mul_eq_one_right
    (exactDiamondLowerSq_mul_inverseSpectralSq ha0 ha1)).symm

theorem exactDirectMetricConstant_eq_forwardSpectralConstant
    (amplitude : ℝ) :
    exactDirectMetricConstant amplitude = forwardSpectralConstant amplitude := by
  unfold exactDirectMetricConstant forwardSpectralConstant
  rw [exactDiamondUpperSq_eq_forwardSpectralSq]

theorem exactInverseMetricConstant_eq_inverseSpectralConstant
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    exactInverseMetricConstant amplitude = inverseSpectralConstant amplitude := by
  unfold exactInverseMetricConstant inverseSpectralConstant
  rw [inverseSpectralSq_eq_inv_exactDiamondLowerSq ha0 ha1]
  rw [Real.sqrt_inv]

theorem forwardSpectralConstant_isLeast_nonnegative_metric
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    IsLeast (ForwardNonnegativeMetricModuli amplitude)
      (forwardSpectralConstant amplitude) := by
  constructor
  · exact ⟨Real.sqrt_nonneg _, forwardSpectralConstant_is_map_metric_bound ha0⟩
  · rintro constant ⟨hc0, hbound⟩
    exact (forward_map_metric_bound_iff ha0 hc0).1 hbound

theorem inverseSpectralConstant_isLeast_nonnegative_metric
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    IsLeast (BackwardNonnegativeMetricModuli amplitude)
      (inverseSpectralConstant amplitude) := by
  constructor
  · exact ⟨Real.sqrt_nonneg _,
      inverseSpectralConstant_is_backward_metric_bound ha0 ha1⟩
  · rintro constant ⟨hc0, hbound⟩
    exact (backward_map_metric_bound_iff ha0 ha1 hc0).1 hbound

theorem exactDirectMetricConstant_isLeast
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    IsLeast (ForwardNonnegativeMetricModuli amplitude)
      (exactDirectMetricConstant amplitude) := by
  rw [exactDirectMetricConstant_eq_forwardSpectralConstant]
  exact forwardSpectralConstant_isLeast_nonnegative_metric ha0

theorem exactInverseMetricConstant_isLeast
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    IsLeast (BackwardNonnegativeMetricModuli amplitude)
      (exactInverseMetricConstant amplitude) := by
  rw [exactInverseMetricConstant_eq_inverseSpectralConstant ha0 ha1]
  exact inverseSpectralConstant_isLeast_nonnegative_metric ha0 ha1

theorem exactMetricConstants_areSimultaneouslyLeast
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    IsLeast (ForwardNonnegativeMetricModuli amplitude)
        (exactDirectMetricConstant amplitude) ∧
      IsLeast (BackwardNonnegativeMetricModuli amplitude)
        (exactInverseMetricConstant amplitude) :=
  ⟨exactDirectMetricConstant_isLeast ha0,
    exactInverseMetricConstant_isLeast ha0 ha1⟩

end

end BoundaryOfSelf.IntrinsicNonradialShearMetricLeastConstants
