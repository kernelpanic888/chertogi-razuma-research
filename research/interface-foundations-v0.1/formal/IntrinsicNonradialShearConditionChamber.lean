import IntrinsicNonradialShearSpectralMap

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearConditionChamber

open StandardHausdorffMetricBridge
open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearKernelSharp
open IntrinsicNonradialShearSpectralMap

theorem forwardSpectralSq_mono
    {first second : ℝ} (hfirst : 0 ≤ first) (horder : first ≤ second) :
    forwardSpectralSq first ≤ forwardSpectralSq second := by
  have hsecond : 0 ≤ second := le_trans hfirst horder
  have hrad :
      first ^ 2 + 2 * first + 2 ≤ second ^ 2 + 2 * second + 2 := by
    nlinarith
  have hsqrt :=
    Real.sqrt_le_sqrt hrad
  have hsqrtFirst :
      0 ≤ Real.sqrt (first ^ 2 + 2 * first + 2) :=
    Real.sqrt_nonneg _
  have hsqrtSecond :
      0 ≤ Real.sqrt (second ^ 2 + 2 * second + 2) :=
    Real.sqrt_nonneg _
  have hproduct :
      first * Real.sqrt (first ^ 2 + 2 * first + 2) ≤
        second * Real.sqrt (second ^ 2 + 2 * second + 2) := by
    calc
      first * Real.sqrt (first ^ 2 + 2 * first + 2) ≤
          second * Real.sqrt (first ^ 2 + 2 * first + 2) :=
        mul_le_mul_of_nonneg_right horder hsqrtFirst
      _ ≤ second * Real.sqrt (second ^ 2 + 2 * second + 2) :=
        mul_le_mul_of_nonneg_left hsqrt hsecond
  dsimp [forwardSpectralSq]
  nlinarith

theorem forwardSpectralConstant_mono
    {first second : ℝ} (hfirst : 0 ≤ first) (horder : first ≤ second) :
    forwardSpectralConstant first ≤ forwardSpectralConstant second := by
  dsimp [forwardSpectralConstant]
  exact Real.sqrt_le_sqrt (forwardSpectralSq_mono hfirst horder)

theorem forwardSpectralSq_strictMono
    {first second : ℝ} (hfirst : 0 ≤ first) (horder : first < second) :
    forwardSpectralSq first < forwardSpectralSq second := by
  have hsecond : 0 ≤ second := le_trans hfirst (le_of_lt horder)
  have hsquares : first ^ 2 ≤ second ^ 2 := by nlinarith
  have hrad :
      first ^ 2 + 2 * first + 2 ≤ second ^ 2 + 2 * second + 2 := by
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hrad
  have hsqrtFirst :
      0 ≤ Real.sqrt (first ^ 2 + 2 * first + 2) :=
    Real.sqrt_nonneg _
  have hproduct :
      first * Real.sqrt (first ^ 2 + 2 * first + 2) ≤
        second * Real.sqrt (second ^ 2 + 2 * second + 2) := by
    calc
      first * Real.sqrt (first ^ 2 + 2 * first + 2) ≤
          second * Real.sqrt (first ^ 2 + 2 * first + 2) :=
        mul_le_mul_of_nonneg_right (le_of_lt horder) hsqrtFirst
      _ ≤ second * Real.sqrt (second ^ 2 + 2 * second + 2) :=
        mul_le_mul_of_nonneg_left hsqrt hsecond
  dsimp [forwardSpectralSq]
  nlinarith

theorem forwardSpectralConstant_strictMono
    {first second : ℝ} (hfirst : 0 ≤ first) (horder : first < second) :
    forwardSpectralConstant first < forwardSpectralConstant second := by
  have hsq := forwardSpectralSq_strictMono hfirst horder
  have hfirstSq0 := forward_spectral_sq_nonneg hfirst
  have hsecond0 : 0 ≤ second := le_trans hfirst (le_of_lt horder)
  have hsecondSq0 := forward_spectral_sq_nonneg hsecond0
  have hfirst0 : 0 ≤ forwardSpectralConstant first := Real.sqrt_nonneg _
  have hsecondC0 : 0 ≤ forwardSpectralConstant second := Real.sqrt_nonneg _
  have hfirst2 :
      forwardSpectralConstant first ^ 2 = forwardSpectralSq first := by
    dsimp [forwardSpectralConstant]
    exact Real.sq_sqrt hfirstSq0
  have hsecond2 :
      forwardSpectralConstant second ^ 2 = forwardSpectralSq second := by
    dsimp [forwardSpectralConstant]
    exact Real.sq_sqrt hsecondSq0
  nlinarith

theorem inverseSpectralParameter_mono
    {first second : ℝ}
    (hfirst : 0 ≤ first) (horder : first ≤ second) (hsecondOne : second < 1) :
    inverseSpectralParameter first ≤ inverseSpectralParameter second := by
  have hfirstDen : 0 < 1 - first := by linarith
  have hsecondDen : 0 < 1 - second := by linarith
  dsimp [inverseSpectralParameter]
  apply (div_le_div_iff₀ hfirstDen hsecondDen).2
  nlinarith

theorem inverseSpectralParameter_strictMono
    {first second : ℝ}
    (hfirst : 0 ≤ first) (horder : first < second) (hsecondOne : second < 1) :
    inverseSpectralParameter first < inverseSpectralParameter second := by
  have hfirstDen : 0 < 1 - first := by linarith
  have hsecondDen : 0 < 1 - second := by linarith
  dsimp [inverseSpectralParameter]
  apply (div_lt_div_iff₀ hfirstDen hsecondDen).2
  nlinarith

theorem inverseSpectralConstant_mono
    {first second : ℝ}
    (hfirst : 0 ≤ first) (horder : first ≤ second) (hsecondOne : second < 1) :
    inverseSpectralConstant first ≤ inverseSpectralConstant second := by
  have hbetaFirst :
      0 ≤ inverseSpectralParameter first :=
    inverseSpectralParameter_nonneg hfirst (by linarith)
  have hbetaOrder :=
    inverseSpectralParameter_mono hfirst horder hsecondOne
  dsimp [inverseSpectralConstant, inverseSpectralSq]
  exact Real.sqrt_le_sqrt
    (forwardSpectralSq_mono hbetaFirst hbetaOrder)

theorem inverseSpectralConstant_strictMono
    {first second : ℝ}
    (hfirst : 0 ≤ first) (horder : first < second) (hsecondOne : second < 1) :
    inverseSpectralConstant first < inverseSpectralConstant second := by
  have hbetaFirst :
      0 ≤ inverseSpectralParameter first :=
    inverseSpectralParameter_nonneg hfirst (by linarith)
  have hbetaOrder :=
    inverseSpectralParameter_strictMono hfirst horder hsecondOne
  dsimp [inverseSpectralConstant, inverseSpectralSq]
  exact forwardSpectralConstant_strictMono hbetaFirst hbetaOrder

noncomputable def conditionNumber (amplitude : ℝ) : ℝ :=
  forwardSpectralConstant amplitude * inverseSpectralConstant amplitude

theorem forwardSpectralConstant_zero :
    forwardSpectralConstant 0 = 1 := by
  norm_num [forwardSpectralConstant, forwardSpectralSq]

theorem inverseSpectralConstant_zero :
    inverseSpectralConstant 0 = 1 := by
  norm_num [inverseSpectralConstant, inverseSpectralSq,
    inverseSpectralParameter, forwardSpectralSq]

theorem conditionNumber_zero :
    conditionNumber 0 = 1 := by
  rw [conditionNumber, forwardSpectralConstant_zero,
    inverseSpectralConstant_zero]
  norm_num

theorem one_add_le_forwardSpectralConstant
    {amplitude : ℝ} (ha : 0 ≤ amplitude) :
    1 + amplitude ≤ forwardSpectralConstant amplitude := by
  let radicand : ℝ := amplitude ^ 2 + 2 * amplitude + 2
  have hrad : 0 ≤ radicand := by
    dsimp [radicand]
    nlinarith
  have hsqrt0 : 0 ≤ Real.sqrt radicand := Real.sqrt_nonneg _
  have hsqrt2 : Real.sqrt radicand ^ 2 = radicand :=
    Real.sq_sqrt hrad
  have hsqrt1 : 1 ≤ Real.sqrt radicand := by
    dsimp [radicand] at hsqrt2 ⊢
    nlinarith
  have hspectral :
      (1 + amplitude) ^ 2 ≤ forwardSpectralSq amplitude := by
    dsimp [forwardSpectralSq, radicand] at hsqrt1 ⊢
    nlinarith
  have hspectral0 := forward_spectral_sq_nonneg ha
  have hconstant0 : 0 ≤ forwardSpectralConstant amplitude := by
    exact Real.sqrt_nonneg _
  have hconstant2 :
      forwardSpectralConstant amplitude ^ 2 =
        forwardSpectralSq amplitude := by
    dsimp [forwardSpectralConstant]
    exact Real.sq_sqrt hspectral0
  nlinarith

theorem one_le_forwardSpectralConstant
    {amplitude : ℝ} (ha : 0 ≤ amplitude) :
    1 ≤ forwardSpectralConstant amplitude := by
  linarith [one_add_le_forwardSpectralConstant ha]

theorem inverse_axial_le_inverseSpectralConstant
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    1 / (1 - amplitude) ≤ inverseSpectralConstant amplitude := by
  have hbeta := inverseSpectralParameter_nonneg ha ha1
  have hbase :=
    one_add_le_forwardSpectralConstant hbeta
  rw [one_add_inverseSpectralParameter ha1] at hbase
  exact hbase

theorem one_le_inverseSpectralConstant
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    1 ≤ inverseSpectralConstant amplitude := by
  have hden : 0 < 1 - amplitude := by linarith
  have hinv : 1 ≤ 1 / (1 - amplitude) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  exact le_trans hinv (inverse_axial_le_inverseSpectralConstant ha ha1)

theorem one_le_conditionNumber
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    1 ≤ conditionNumber amplitude := by
  have hforward := one_le_forwardSpectralConstant ha
  have hinverse := one_le_inverseSpectralConstant ha ha1
  dsimp [conditionNumber]
  nlinarith

theorem conditionNumber_mono
    {first second : ℝ}
    (hfirst : 0 ≤ first) (horder : first ≤ second) (hsecondOne : second < 1) :
    conditionNumber first ≤ conditionNumber second := by
  have hforward :=
    forwardSpectralConstant_mono hfirst horder
  have hinverse :=
    inverseSpectralConstant_mono hfirst horder hsecondOne
  have hf0 : 0 ≤ forwardSpectralConstant first := Real.sqrt_nonneg _
  have hi0 : 0 ≤ inverseSpectralConstant first := Real.sqrt_nonneg _
  have hf20 : 0 ≤ forwardSpectralConstant second := Real.sqrt_nonneg _
  have hi20 : 0 ≤ inverseSpectralConstant second := Real.sqrt_nonneg _
  dsimp [conditionNumber]
  exact mul_le_mul hforward hinverse hi0 hf20

theorem conditionNumber_strictMono
    {first second : ℝ}
    (hfirst : 0 ≤ first) (horder : first < second) (hsecondOne : second < 1) :
    conditionNumber first < conditionNumber second := by
  have hforward :=
    forwardSpectralConstant_strictMono hfirst horder
  have hinverse :=
    inverseSpectralConstant_mono hfirst (le_of_lt horder) hsecondOne
  have hfirstOne :=
    one_le_inverseSpectralConstant hfirst (by linarith)
  have hsecondForward0 :
      0 ≤ forwardSpectralConstant second := Real.sqrt_nonneg _
  dsimp [conditionNumber]
  calc
    forwardSpectralConstant first * inverseSpectralConstant first <
        forwardSpectralConstant second * inverseSpectralConstant first :=
      mul_lt_mul_of_pos_right hforward (lt_of_lt_of_le zero_lt_one hfirstOne)
    _ ≤ forwardSpectralConstant second * inverseSpectralConstant second :=
      mul_le_mul_of_nonneg_left hinverse hsecondForward0

theorem forwardSpectralConstant_injective_on_nonnegative
    {first second : ℝ} (hfirst : 0 ≤ first) (hsecond : 0 ≤ second)
    (hequal : forwardSpectralConstant first =
      forwardSpectralConstant second) :
    first = second := by
  rcases lt_trichotomy first second with hlt | heq | hgt
  · have := forwardSpectralConstant_strictMono hfirst hlt
    linarith
  · exact heq
  · have := forwardSpectralConstant_strictMono hsecond hgt
    linarith

theorem inverseSpectralConstant_injective_on_chamber
    {first second : ℝ}
    (hfirst : 0 ≤ first) (hfirstOne : first < 1)
    (hsecond : 0 ≤ second) (hsecondOne : second < 1)
    (hequal : inverseSpectralConstant first =
      inverseSpectralConstant second) :
    first = second := by
  rcases lt_trichotomy first second with hlt | heq | hgt
  · have := inverseSpectralConstant_strictMono hfirst hlt hsecondOne
    linarith
  · exact heq
  · have := inverseSpectralConstant_strictMono hsecond hgt hfirstOne
    linarith

theorem conditionNumber_injective_on_chamber
    {first second : ℝ}
    (hfirst : 0 ≤ first) (hfirstOne : first < 1)
    (hsecond : 0 ≤ second) (hsecondOne : second < 1)
    (hequal : conditionNumber first = conditionNumber second) :
    first = second := by
  rcases lt_trichotomy first second with hlt | heq | hgt
  · have := conditionNumber_strictMono hfirst hlt hsecondOne
    linarith
  · exact heq
  · have := conditionNumber_strictMono hsecond hgt hfirstOne
    linarith

def DistortionObservation
    (amplitude forwardObserved backwardObserved : ℝ) : Prop :=
  ForwardMapMetricBound amplitude forwardObserved ∧
    BackwardMapMetricBound amplitude backwardObserved

theorem distortionObservation_iff_exactConstants
    {amplitude forwardObserved backwardObserved : ℝ}
    (ha : 0 ≤ amplitude) (ha1 : amplitude < 1)
    (hf : 0 ≤ forwardObserved) (hb : 0 ≤ backwardObserved) :
    DistortionObservation amplitude forwardObserved backwardObserved ↔
      forwardSpectralConstant amplitude ≤ forwardObserved ∧
        inverseSpectralConstant amplitude ≤ backwardObserved := by
  constructor
  · intro h
    exact ⟨
      (forward_map_metric_bound_iff ha hf).1 h.1,
      (backward_map_metric_bound_iff ha ha1 hb).1 h.2⟩
  · intro h
    exact ⟨
      (forward_map_metric_bound_iff ha hf).2 h.1,
      (backward_map_metric_bound_iff ha ha1 hb).2 h.2⟩

def FeasibleAmplitude
    (forwardObserved backwardObserved amplitude : ℝ) : Prop :=
  0 ≤ amplitude ∧ amplitude < 1 ∧
    forwardSpectralConstant amplitude ≤ forwardObserved ∧
    inverseSpectralConstant amplitude ≤ backwardObserved

theorem feasibleAmplitude_downward
    {forwardObserved backwardObserved first second : ℝ}
    (hfirst : FeasibleAmplitude forwardObserved backwardObserved first)
    (hsecond0 : 0 ≤ second) (horder : second ≤ first) :
    FeasibleAmplitude forwardObserved backwardObserved second := by
  rcases hfirst with ⟨hfirst0, hfirst1, hforward, hinverse⟩
  have hsecond1 : second < 1 := lt_of_le_of_lt horder hfirst1
  refine ⟨hsecond0, hsecond1, ?_, ?_⟩
  · exact le_trans
      (forwardSpectralConstant_mono hsecond0 horder) hforward
  · exact le_trans
      (inverseSpectralConstant_mono hsecond0 horder hfirst1) hinverse

theorem observed_distortion_bounds_amplitude
    {amplitude forwardObserved backwardObserved : ℝ}
    (ha : 0 ≤ amplitude) (ha1 : amplitude < 1)
    (hf : 0 ≤ forwardObserved) (hb : 0 ≤ backwardObserved)
    (hobs : DistortionObservation amplitude forwardObserved backwardObserved) :
    amplitude ≤
      min (forwardObserved - 1)
        ((backwardObserved - 1) / backwardObserved) := by
  have hexact :=
    (distortionObservation_iff_exactConstants ha ha1 hf hb).1 hobs
  have hforwardBase := one_add_le_forwardSpectralConstant ha
  have hforward : amplitude ≤ forwardObserved - 1 := by linarith
  have hinverseBase :=
    inverse_axial_le_inverseSpectralConstant ha ha1
  have hbackwardOne :
      1 ≤ backwardObserved := by
    have hden : 0 < 1 - amplitude := by linarith
    have hone : 1 ≤ 1 / (1 - amplitude) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    exact le_trans hone (le_trans hinverseBase hexact.2)
  have hbackwardPos : 0 < backwardObserved := lt_of_lt_of_le zero_lt_one hbackwardOne
  have hscaled :
      1 ≤ backwardObserved * (1 - amplitude) := by
    have hden : 0 < 1 - amplitude := by linarith
    have h := le_trans hinverseBase hexact.2
    exact (div_le_iff₀ hden).1 h
  have hbackward :
      amplitude ≤ (backwardObserved - 1) / backwardObserved := by
    apply (le_div_iff₀ hbackwardPos).2
    nlinarith
  exact le_min hforward hbackward

theorem forward_threshold_excludes_candidate
    {actual candidate observed : ℝ}
    (hactual0 : 0 ≤ actual) (hcandidate0 : 0 ≤ candidate)
    (hobserved : forwardSpectralConstant actual ≤ observed)
    (hthreshold : observed < forwardSpectralConstant candidate) :
    actual < candidate := by
  by_contra hnot
  have horder : candidate ≤ actual := le_of_not_gt hnot
  have hmono :=
    forwardSpectralConstant_mono hcandidate0 horder
  linarith

theorem inverse_threshold_excludes_candidate
    {actual candidate observed : ℝ}
    (hactual0 : 0 ≤ actual) (hactual1 : actual < 1)
    (hcandidate0 : 0 ≤ candidate) (hcandidate1 : candidate < 1)
    (hobserved : inverseSpectralConstant actual ≤ observed)
    (hthreshold : observed < inverseSpectralConstant candidate) :
    actual < candidate := by
  by_contra hnot
  have horder : candidate ≤ actual := le_of_not_gt hnot
  have hmono :=
    inverseSpectralConstant_mono hcandidate0 horder hactual1
  linarith

end BoundaryOfSelf.IntrinsicNonradialShearConditionChamber
