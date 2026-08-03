import IntrinsicNonradialShearNoisyIdentifiability
import IntrinsicNonradialShearRealizableCertificate
import IntrinsicNonradialShearSharpEnvelope

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearRawSampleCertification

noncomputable section

open IntrinsicNonradialShearDeltaNet
open IntrinsicNonradialShearClosedCore
open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearDiagonalBlowUpInverse
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearRealizableClosure
open IntrinsicNonradialShearRealizableCertificate
open IntrinsicNonradialShearSharpEnvelope
open IntrinsicNonradialShearMetricLeastConstants
open IntrinsicNonradialShearNoisyIdentifiability

/-! ## IF-BS-22F-F8C29: raw finite sample to certified error budgets -/

noncomputable def rawSampleLower {α : Type*} :
    List (NoisyUpperReading α) → ℝ
  | [] => 0
  | reading :: rest =>
      max (reading.measured - reading.error) (rawSampleLower rest)

def rawSquareUpper {α : Type*}
    (sample : List (NoisyUpperReading α))
    (regularity delta : ℝ) : ℝ :=
  noisySampleUpper sample + regularity * delta

def rawMetricObserved {α : Type*}
    (sample : List (NoisyUpperReading α))
    (regularity delta : ℝ) : ℝ :=
  Real.sqrt (rawSquareUpper sample regularity delta)

def rawMetricError {α : Type*}
    (sample : List (NoisyUpperReading α))
    (regularity delta : ℝ) : ℝ :=
  Real.sqrt (rawSquareUpper sample regularity delta) -
    Real.sqrt (rawSampleLower sample)

def SplitBudgetSampleValid {α : Type*}
    (value : α → ℝ) (sample : List (NoisyUpperReading α))
    (instrumentNoise computationalResolution : ℝ) : Prop :=
  0 ≤ instrumentNoise ∧ 0 ≤ computationalResolution ∧
    ∀ reading, reading ∈ sample →
      reading.error = instrumentNoise + computationalResolution ∧
      |reading.measured - value reading.point| ≤
        instrumentNoise + computationalResolution

structure RawFiniteMaximumCertificate
    {α : Type*} [PseudoMetricSpace α]
    (domain : Set α) (value : α → ℝ) (exactMaximum : ℝ)
    (sample : List (NoisyUpperReading α))
    (regularity delta : ℝ) : Prop where
  delta_nonneg : 0 ≤ delta
  regularity_nonneg : 0 ≤ regularity
  exact_nonneg : 0 ≤ exactMaximum
  sample_valid : NoisyUpperSampleValid value sample
  coverage : DeltaCoverage domain sample delta
  sample_inside : ∀ reading, reading ∈ sample → reading.point ∈ domain
  regularity_certificate :
    RegularityCertificate domain sample regularity value
  exact_isGreatest : IsGreatest (value '' domain) exactMaximum

theorem splitBudgetSampleValid_implies_noisyUpperSampleValid
    {α : Type*} {value : α → ℝ}
    {sample : List (NoisyUpperReading α)}
    {instrumentNoise computationalResolution : ℝ}
    (hsplit : SplitBudgetSampleValid value sample
      instrumentNoise computationalResolution) :
    NoisyUpperSampleValid value sample := by
  intro reading hreading
  have h := hsplit.2.2 reading hreading
  constructor
  · rw [h.1]
    exact add_nonneg hsplit.1 hsplit.2.1
  · rw [h.1]
    exact h.2

lemma rawSampleLower_nonneg
    {α : Type*} (sample : List (NoisyUpperReading α)) :
    0 ≤ rawSampleLower sample := by
  induction sample with
  | nil => simp [rawSampleLower]
  | cons reading rest ih =>
      rw [rawSampleLower]
      exact le_max_of_le_right ih

lemma rawSampleLower_le_of
    {α : Type*} {sample : List (NoisyUpperReading α)}
    {upper : ℝ} (hupper : 0 ≤ upper)
    (hreading : ∀ reading, reading ∈ sample →
      reading.measured - reading.error ≤ upper) :
    rawSampleLower sample ≤ upper := by
  induction sample with
  | nil => simpa [rawSampleLower] using hupper
  | cons head rest ih =>
      rw [rawSampleLower]
      apply max_le
      · exact hreading head (by simp)
      · apply ih
        intro reading hmem
        exact hreading reading (by simp [hmem])

theorem rawSampleLower_le_exactMaximum
    {α : Type*} [PseudoMetricSpace α]
    {domain : Set α} {value : α → ℝ} {exactMaximum : ℝ}
    {sample : List (NoisyUpperReading α)}
    {regularity delta : ℝ}
    (hcert : RawFiniteMaximumCertificate domain value exactMaximum
      sample regularity delta) :
    rawSampleLower sample ≤ exactMaximum := by
  apply rawSampleLower_le_of hcert.exact_nonneg
  intro reading hmem
  have hvalid := hcert.sample_valid reading hmem
  have herror := (abs_le.mp hvalid.2).2
  have htrue : reading.measured - reading.error ≤ value reading.point := by
    linarith
  have hdomain : value reading.point ∈ value '' domain :=
    ⟨reading.point, hcert.sample_inside reading hmem, rfl⟩
  exact le_trans htrue (hcert.exact_isGreatest.2 hdomain)

theorem exactMaximum_le_rawSquareUpper
    {α : Type*} [PseudoMetricSpace α]
    {domain : Set α} {value : α → ℝ} {exactMaximum : ℝ}
    {sample : List (NoisyUpperReading α)}
    {regularity delta : ℝ}
    (hcert : RawFiniteMaximumCertificate domain value exactMaximum
      sample regularity delta) :
    exactMaximum ≤ rawSquareUpper sample regularity delta := by
  rcases hcert.exact_isGreatest.1 with ⟨point, hpoint, hvalue⟩
  rw [← hvalue]
  exact global_le_noisySampleUpper_add_regularity
    hcert.regularity_nonneg hcert.sample_valid hcert.coverage
      hcert.regularity_certificate point hpoint

theorem rawSquare_interval
    {α : Type*} [PseudoMetricSpace α]
    {domain : Set α} {value : α → ℝ} {exactMaximum : ℝ}
    {sample : List (NoisyUpperReading α)}
    {regularity delta : ℝ}
    (hcert : RawFiniteMaximumCertificate domain value exactMaximum
      sample regularity delta) :
    exactMaximum ∈ Set.Icc (rawSampleLower sample)
      (rawSquareUpper sample regularity delta) :=
  ⟨rawSampleLower_le_exactMaximum hcert,
    exactMaximum_le_rawSquareUpper hcert⟩

theorem rawMetricError_nonneg
    {α : Type*} [PseudoMetricSpace α]
    {domain : Set α} {value : α → ℝ} {exactMaximum : ℝ}
    {sample : List (NoisyUpperReading α)}
    {regularity delta : ℝ}
    (hcert : RawFiniteMaximumCertificate domain value exactMaximum
      sample regularity delta) :
    0 ≤ rawMetricError sample regularity delta := by
  unfold rawMetricError
  exact sub_nonneg.mpr (Real.sqrt_le_sqrt
    (le_trans (rawSampleLower_le_exactMaximum hcert)
      (exactMaximum_le_rawSquareUpper hcert)))

theorem rawMetricObserved_error_bound
    {α : Type*} [PseudoMetricSpace α]
    {domain : Set α} {value : α → ℝ} {exactMaximum : ℝ}
    {sample : List (NoisyUpperReading α)}
    {regularity delta : ℝ}
    (hcert : RawFiniteMaximumCertificate domain value exactMaximum
      sample regularity delta) :
    |rawMetricObserved sample regularity delta -
        Real.sqrt exactMaximum| ≤
      rawMetricError sample regularity delta := by
  have hlower := Real.sqrt_le_sqrt
    (rawSampleLower_le_exactMaximum hcert)
  have hupper := Real.sqrt_le_sqrt
    (exactMaximum_le_rawSquareUpper hcert)
  unfold rawMetricObserved rawMetricError
  rw [abs_of_nonneg (sub_nonneg.mpr hupper)]
  linarith

lemma fullInverseRegularity_nonneg
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    0 ≤ sharpDiamondInverseRegularity amplitude := by
  unfold sharpDiamondInverseRegularity
  exact div_nonneg (forwardBlowUpSqRegularity_nonneg ha0) (sq_nonneg _)

theorem fullInverse_diamond_regularity_bound
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1)
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand) :
    |inverseBlowUpSq amplitude first - inverseBlowUpSq amplitude second| ≤
      sharpDiamondInverseRegularity amplitude * dist first second := by
  have hreg := forwardBlowUpSq_regularity_bound ha0 first
    (diamond_mem_relaxedChamber hfirst) second
    (diamond_mem_relaxedChamber hsecond)
  have henv_first := exactDiamond_lower_bound ha0 ha1 hfirst
  have henv_second := exactDiamond_lower_bound ha0 ha1 hsecond
  have hlower_pos := exactDiamondLowerSq_pos ha0 ha1
  have hf_pos : 0 < forwardBlowUpSq amplitude first :=
    lt_of_lt_of_le hlower_pos henv_first
  have hs_pos : 0 < forwardBlowUpSq amplitude second :=
    lt_of_lt_of_le hlower_pos henv_second
  have hden : exactDiamondLowerSq amplitude ^ 2 ≤
      |forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second| := by
    have hraw : exactDiamondLowerSq amplitude * exactDiamondLowerSq amplitude ≤
        forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second :=
      mul_le_mul henv_first henv_second (le_of_lt hlower_pos)
        (le_trans (le_of_lt hlower_pos) henv_first)
    simpa [pow_two, abs_mul, abs_of_pos hf_pos, abs_of_pos hs_pos] using hraw
  have hlower_sq_pos : 0 < exactDiamondLowerSq amplitude ^ 2 :=
    sq_pos_of_pos hlower_pos
  have hnum : |forwardBlowUpSq amplitude second -
      forwardBlowUpSq amplitude first| ≤
        forwardBlowUpSqRegularity amplitude * dist first second := by
    simpa [abs_sub_comm] using hreg
  have htarget_nonneg : 0 ≤
      forwardBlowUpSqRegularity amplitude * dist first second :=
    mul_nonneg (forwardBlowUpSqRegularity_nonneg ha0) dist_nonneg
  have hfrac : |forwardBlowUpSq amplitude second -
        forwardBlowUpSq amplitude first| /
      |forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second| ≤
        (forwardBlowUpSqRegularity amplitude * dist first second) /
          exactDiamondLowerSq amplitude ^ 2 := by
    exact div_le_div₀ htarget_nonneg hnum hlower_sq_pos hden
  change |(forwardBlowUpSq amplitude first)⁻¹ -
      (forwardBlowUpSq amplitude second)⁻¹| ≤ _
  rw [inv_sub_inv hf_pos.ne' hs_pos.ne', abs_div]
  calc
    |forwardBlowUpSq amplitude second - forwardBlowUpSq amplitude first| /
          |forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second| ≤
        (forwardBlowUpSqRegularity amplitude * dist first second) /
          exactDiamondLowerSq amplitude ^ 2 := hfrac
    _ = sharpDiamondInverseRegularity amplitude * dist first second := by
      unfold sharpDiamondInverseRegularity
      field_simp [ne_of_gt hlower_sq_pos]

theorem forward_raw_finite_certificate
    {amplitude delta : ℝ}
    {sample : List (NoisyUpperReading BlowUpPoint)}
    (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) (hdelta : 0 ≤ delta)
    (hvalid : NoisyUpperSampleValid (forwardBlowUpSq amplitude) sample)
    (hcoverage : DeltaCoverage directionalDiamondBand sample delta)
    (hinside : ∀ reading, reading ∈ sample →
      reading.point ∈ directionalDiamondBand) :
    RawFiniteMaximumCertificate directionalDiamondBand
      (forwardBlowUpSq amplitude) (exactDiamondUpperSq amplitude)
      sample (forwardBlowUpSqRegularity amplitude) delta := by
  refine
    { delta_nonneg := hdelta
      regularity_nonneg := forwardBlowUpSqRegularity_nonneg ha0
      exact_nonneg := le_of_lt (exactDiamondUpperSq_pos ha0)
      sample_valid := hvalid
      coverage := hcoverage
      sample_inside := hinside
      regularity_certificate := ?_
      exact_isGreatest := (exactDiamond_envelope_isSharp ha0 ha1).2 }
  intro point hpoint reading hreading
  exact forward_diamond_regularity_bound ha0 point hpoint
    reading.point (hinside reading hreading)

theorem inverse_raw_finite_certificate
    {amplitude delta : ℝ}
    {sample : List (NoisyUpperReading BlowUpPoint)}
    (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) (hdelta : 0 ≤ delta)
    (hvalid : NoisyUpperSampleValid (inverseBlowUpSq amplitude) sample)
    (hcoverage : DeltaCoverage directionalDiamondBand sample delta)
    (hinside : ∀ reading, reading ∈ sample →
      reading.point ∈ directionalDiamondBand) :
    RawFiniteMaximumCertificate directionalDiamondBand
      (inverseBlowUpSq amplitude) (exactDiamondLowerSq amplitude)⁻¹
      sample (sharpDiamondInverseRegularity amplitude) delta := by
  refine
    { delta_nonneg := hdelta
      regularity_nonneg := fullInverseRegularity_nonneg ha0
      exact_nonneg := le_of_lt (inv_pos.mpr
        (exactDiamondLowerSq_pos ha0 ha1))
      sample_valid := hvalid
      coverage := hcoverage
      sample_inside := hinside
      regularity_certificate := ?_
      exact_isGreatest := ?_ }
  · intro point hpoint reading hreading
    exact fullInverse_diamond_regularity_bound ha0 ha1 hpoint
      (hinside reading hreading)
  · constructor
    · refine ⟨lowerDiamondWitness amplitude,
        lowerDiamondWitness_mem ha0 ha1, ?_⟩
      rw [inverseBlowUpSq, lowerDiamondWitness_exact ha0 ha1]
    · rintro _ ⟨point, hpoint, rfl⟩
      have hlower := exactDiamond_lower_bound ha0 ha1 hpoint
      have hpointPos : 0 < forwardBlowUpSq amplitude point :=
        lt_of_lt_of_le (exactDiamondLowerSq_pos ha0 ha1) hlower
      exact (inv_le_inv₀ hpointPos (exactDiamondLowerSq_pos ha0 ha1)).2 hlower

theorem raw_finite_samples_certify_noisy_reading
    {amplitude forwardDelta inverseDelta
      forwardInstrument forwardResolution
      inverseInstrument inverseResolution : ℝ}
    {forwardSample inverseSample : List (NoisyUpperReading BlowUpPoint)}
    (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1)
    (hforwardDelta : 0 ≤ forwardDelta)
    (hinverseDelta : 0 ≤ inverseDelta)
    (hforwardSplit : SplitBudgetSampleValid
      (forwardBlowUpSq amplitude) forwardSample
      forwardInstrument forwardResolution)
    (hinverseSplit : SplitBudgetSampleValid
      (inverseBlowUpSq amplitude) inverseSample
      inverseInstrument inverseResolution)
    (hforwardCoverage :
      DeltaCoverage directionalDiamondBand forwardSample forwardDelta)
    (hinverseCoverage :
      DeltaCoverage directionalDiamondBand inverseSample inverseDelta)
    (hforwardInside : ∀ reading, reading ∈ forwardSample →
      reading.point ∈ directionalDiamondBand)
    (hinverseInside : ∀ reading, reading ∈ inverseSample →
      reading.point ∈ directionalDiamondBand) :
    CertifiedNoisyMetricReading amplitude
      (rawMetricObserved forwardSample
        (forwardBlowUpSqRegularity amplitude) forwardDelta)
      (rawMetricObserved inverseSample
        (sharpDiamondInverseRegularity amplitude) inverseDelta)
      (rawMetricError forwardSample
        (forwardBlowUpSqRegularity amplitude) forwardDelta)
      (rawMetricError inverseSample
        (sharpDiamondInverseRegularity amplitude) inverseDelta) := by
  have hfvalid :=
    splitBudgetSampleValid_implies_noisyUpperSampleValid hforwardSplit
  have hivalid :=
    splitBudgetSampleValid_implies_noisyUpperSampleValid hinverseSplit
  let hforward := forward_raw_finite_certificate ha0 ha1 hforwardDelta
    hfvalid hforwardCoverage hforwardInside
  let hinverse := inverse_raw_finite_certificate ha0 ha1 hinverseDelta
    hivalid hinverseCoverage hinverseInside
  refine ⟨ha0, ha1, rawMetricError_nonneg hforward,
    rawMetricError_nonneg hinverse, ?_, ?_⟩
  · simpa [exactDirectMetricConstant] using
      rawMetricObserved_error_bound hforward
  · have hbound := rawMetricObserved_error_bound hinverse
    rw [Real.sqrt_inv] at hbound
    simpa [exactInverseMetricConstant] using hbound

end

end BoundaryOfSelf.IntrinsicNonradialShearRawSampleCertification
