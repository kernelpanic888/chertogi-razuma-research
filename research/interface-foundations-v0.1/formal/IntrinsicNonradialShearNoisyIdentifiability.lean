import IntrinsicNonradialShearMetricLeastConstants

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearNoisyIdentifiability

noncomputable section

open IntrinsicNonradialShearExactSupport
open IntrinsicNonradialShearSpectralMap
open IntrinsicNonradialShearConditionChamber
open IntrinsicNonradialShearMetricLeastConstants

/-! ## IF-BS-22F-F8C28: certified noisy identifiability chamber -/

def CertifiedNoisyMetricReading
    (amplitude forwardObserved inverseObserved
      forwardError inverseError : ℝ) : Prop :=
  0 ≤ amplitude ∧ amplitude < 1 ∧
    0 ≤ forwardError ∧ 0 ≤ inverseError ∧
    |forwardObserved - exactDirectMetricConstant amplitude| ≤ forwardError ∧
    |inverseObserved - exactInverseMetricConstant amplitude| ≤ inverseError

def NoisyFeasibleAmplitudes
    (forwardObserved inverseObserved forwardError inverseError : ℝ) : Set ℝ :=
  {amplitude | CertifiedNoisyMetricReading amplitude
    forwardObserved inverseObserved forwardError inverseError}

def noisyAmplitudeLower
    (forwardObserved forwardError : ℝ) : ℝ :=
  max 0 ((forwardObserved - forwardError - 1) / Real.sqrt 2)

def noisyAmplitudeUpper
    (forwardObserved inverseObserved forwardError inverseError : ℝ) : ℝ :=
  min (forwardObserved + forwardError - 1)
    ((inverseObserved + inverseError - 1) /
      (inverseObserved + inverseError))

theorem exactDirectMetricConstant_le_sqrtTwoEnvelope
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    exactDirectMetricConstant amplitude ≤ 1 + Real.sqrt 2 * amplitude := by
  have hleast := exactDirectMetricConstant_isLeast ha0
  apply hleast.2
  exact ⟨by positivity, fun first second =>
    intrinsicShearMap_dist_le_sqrt_two amplitude ha0 first second⟩

theorem certified_reading_direct_bounds
    {amplitude forwardObserved inverseObserved forwardError inverseError : ℝ}
    (hreading : CertifiedNoisyMetricReading amplitude
      forwardObserved inverseObserved forwardError inverseError) :
    forwardObserved - forwardError ≤ exactDirectMetricConstant amplitude ∧
      exactDirectMetricConstant amplitude ≤ forwardObserved + forwardError := by
  rcases hreading with ⟨_ha0, _ha1, _hfe0, _hie0, hforward, _hinverse⟩
  rcases abs_le.mp hforward with ⟨hleft, hright⟩
  constructor <;> linarith

theorem certified_reading_inverse_bounds
    {amplitude forwardObserved inverseObserved forwardError inverseError : ℝ}
    (hreading : CertifiedNoisyMetricReading amplitude
      forwardObserved inverseObserved forwardError inverseError) :
    inverseObserved - inverseError ≤ exactInverseMetricConstant amplitude ∧
      exactInverseMetricConstant amplitude ≤ inverseObserved + inverseError := by
  rcases hreading with ⟨_ha0, _ha1, _hfe0, _hie0, _hforward, hinverse⟩
  rcases abs_le.mp hinverse with ⟨hleft, hright⟩
  constructor <;> linarith

theorem certified_reading_lower_bound
    {amplitude forwardObserved inverseObserved forwardError inverseError : ℝ}
    (hreading : CertifiedNoisyMetricReading amplitude
      forwardObserved inverseObserved forwardError inverseError) :
    noisyAmplitudeLower forwardObserved forwardError ≤ amplitude := by
  have ha0 := hreading.1
  have hobserved := (certified_reading_direct_bounds hreading).1
  have hcoarse := exactDirectMetricConstant_le_sqrtTwoEnvelope ha0
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hraw :
      (forwardObserved - forwardError - 1) / Real.sqrt 2 ≤ amplitude := by
    apply (div_le_iff₀ hsqrt).2
    nlinarith
  exact max_le ha0 hraw

theorem certified_reading_forward_upper_bound
    {amplitude forwardObserved inverseObserved forwardError inverseError : ℝ}
    (hreading : CertifiedNoisyMetricReading amplitude
      forwardObserved inverseObserved forwardError inverseError) :
    amplitude ≤ forwardObserved + forwardError - 1 := by
  have ha0 := hreading.1
  have hbase :
      1 + amplitude ≤ exactDirectMetricConstant amplitude := by
    rw [exactDirectMetricConstant_eq_forwardSpectralConstant]
    exact one_add_le_forwardSpectralConstant ha0
  have hobserved := (certified_reading_direct_bounds hreading).2
  linarith

theorem certified_reading_inverse_upper_bound
    {amplitude forwardObserved inverseObserved forwardError inverseError : ℝ}
    (hreading : CertifiedNoisyMetricReading amplitude
      forwardObserved inverseObserved forwardError inverseError) :
    amplitude ≤ (inverseObserved + inverseError - 1) /
      (inverseObserved + inverseError) := by
  let observed : ℝ := inverseObserved + inverseError
  have ha0 := hreading.1
  have ha1 := hreading.2.1
  have hden : 0 < 1 - amplitude := by linarith
  have haxial :
      1 / (1 - amplitude) ≤ exactInverseMetricConstant amplitude := by
    rw [exactInverseMetricConstant_eq_inverseSpectralConstant ha0 ha1]
    exact inverse_axial_le_inverseSpectralConstant ha0 ha1
  have hreadingUpper := (certified_reading_inverse_bounds hreading).2
  have hreciprocal : 1 / (1 - amplitude) ≤ observed := by
    exact le_trans haxial (by simpa [observed] using hreadingUpper)
  have hobserved : 0 < observed :=
    lt_of_lt_of_le (one_div_pos.mpr hden) hreciprocal
  have hmul : 1 ≤ observed * (1 - amplitude) :=
    (div_le_iff₀ hden).1 hreciprocal
  change amplitude ≤ (observed - 1) / observed
  apply (le_div_iff₀ hobserved).2
  nlinarith

theorem certified_reading_amplitude_mem_interval
    {amplitude forwardObserved inverseObserved forwardError inverseError : ℝ}
    (hreading : CertifiedNoisyMetricReading amplitude
      forwardObserved inverseObserved forwardError inverseError) :
    amplitude ∈ Set.Icc
      (noisyAmplitudeLower forwardObserved forwardError)
      (noisyAmplitudeUpper forwardObserved inverseObserved
        forwardError inverseError) := by
  constructor
  · exact certified_reading_lower_bound hreading
  · rw [noisyAmplitudeUpper]
    exact le_min
      (certified_reading_forward_upper_bound hreading)
      (certified_reading_inverse_upper_bound hreading)

theorem noisyFeasibleAmplitudes_subset_interval
    (forwardObserved inverseObserved forwardError inverseError : ℝ) :
    NoisyFeasibleAmplitudes forwardObserved inverseObserved
        forwardError inverseError ⊆
      Set.Icc (noisyAmplitudeLower forwardObserved forwardError)
        (noisyAmplitudeUpper forwardObserved inverseObserved
          forwardError inverseError) := by
  intro amplitude hreading
  exact certified_reading_amplitude_mem_interval hreading

theorem certified_reading_feasible_nonempty
    {amplitude forwardObserved inverseObserved forwardError inverseError : ℝ}
    (hreading : CertifiedNoisyMetricReading amplitude
      forwardObserved inverseObserved forwardError inverseError) :
    (NoisyFeasibleAmplitudes forwardObserved inverseObserved
      forwardError inverseError).Nonempty :=
  ⟨amplitude, hreading⟩

theorem zero_error_reading_unique
    {forwardObserved inverseObserved first second : ℝ}
    (hfirst : CertifiedNoisyMetricReading first
      forwardObserved inverseObserved 0 0)
    (hsecond : CertifiedNoisyMetricReading second
      forwardObserved inverseObserved 0 0) :
    first = second := by
  have hfirstAbs := hfirst.2.2.2.2.1
  have hsecondAbs := hsecond.2.2.2.2.1
  have hfirstZero :
      |forwardObserved - exactDirectMetricConstant first| = 0 :=
    le_antisymm hfirstAbs (abs_nonneg _)
  have hsecondZero :
      |forwardObserved - exactDirectMetricConstant second| = 0 :=
    le_antisymm hsecondAbs (abs_nonneg _)
  have hfirstEq :
      forwardObserved = exactDirectMetricConstant first :=
    sub_eq_zero.mp (abs_eq_zero.mp hfirstZero)
  have hsecondEq :
      forwardObserved = exactDirectMetricConstant second :=
    sub_eq_zero.mp (abs_eq_zero.mp hsecondZero)
  have hconstants :
      exactDirectMetricConstant first = exactDirectMetricConstant second :=
    hfirstEq.symm.trans hsecondEq
  rw [exactDirectMetricConstant_eq_forwardSpectralConstant,
    exactDirectMetricConstant_eq_forwardSpectralConstant] at hconstants
  exact forwardSpectralConstant_injective_on_nonnegative
    hfirst.1 hsecond.1 hconstants

end

end BoundaryOfSelf.IntrinsicNonradialShearNoisyIdentifiability
