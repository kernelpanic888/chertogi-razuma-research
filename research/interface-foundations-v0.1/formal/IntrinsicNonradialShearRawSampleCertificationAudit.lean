import IntrinsicNonradialShearRawSampleCertification

namespace BoundaryOfSelf.IntrinsicNonradialShearRawSampleCertificationAudit

open Set
open IntrinsicNonradialShearDeltaNet
open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearDiagonalBlowUpInverse
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearRealizableClosure
open IntrinsicNonradialShearSharpEnvelope
open IntrinsicNonradialShearNoisyIdentifiability
open IntrinsicNonradialShearRawSampleCertification

theorem audited_square_interval
    {α : Type*} [PseudoMetricSpace α]
    {domain : Set α} {value : α → ℝ} {exactMaximum : ℝ}
    {sample : List (NoisyUpperReading α)}
    {regularity delta : ℝ}
    (hcert : RawFiniteMaximumCertificate domain value exactMaximum
      sample regularity delta) :
    exactMaximum ∈ Set.Icc (rawSampleLower sample)
      (rawSquareUpper sample regularity delta) :=
  rawSquare_interval hcert

theorem audited_root_transport
    {α : Type*} [PseudoMetricSpace α]
    {domain : Set α} {value : α → ℝ} {exactMaximum : ℝ}
    {sample : List (NoisyUpperReading α)}
    {regularity delta : ℝ}
    (hcert : RawFiniteMaximumCertificate domain value exactMaximum
      sample regularity delta) :
    |rawMetricObserved sample regularity delta -
        Real.sqrt exactMaximum| ≤
      rawMetricError sample regularity delta :=
  rawMetricObserved_error_bound hcert

theorem audited_full_inverse_regularity
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1)
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand) :
    |inverseBlowUpSq amplitude first - inverseBlowUpSq amplitude second| ≤
      sharpDiamondInverseRegularity amplitude * dist first second :=
  fullInverse_diamond_regularity_bound ha0 ha1 hfirst hsecond

theorem audited_raw_pipeline
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
        (sharpDiamondInverseRegularity amplitude) inverseDelta) :=
  raw_finite_samples_certify_noisy_reading ha0 ha1
    hforwardDelta hinverseDelta hforwardSplit hinverseSplit
    hforwardCoverage hinverseCoverage hforwardInside hinverseInside

#print axioms audited_square_interval
#print axioms audited_root_transport
#print axioms audited_full_inverse_regularity
#print axioms audited_raw_pipeline

end BoundaryOfSelf.IntrinsicNonradialShearRawSampleCertificationAudit
