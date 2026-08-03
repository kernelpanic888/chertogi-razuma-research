import IntrinsicNonradialShearRawSampleCertification

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearExecutableCoarseNet

noncomputable section

open StandardHausdorffMetricBridge
open LocalSegmentRealCompletion
open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearExactSupport
open IntrinsicNonradialShearKernelSharp
open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearDiagonalBlowUpInverse
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearRealizableClosure
open IntrinsicNonradialShearDeltaNet
open IntrinsicNonradialShearSharpEnvelope
open IntrinsicNonradialShearNoisyIdentifiability
open IntrinsicNonradialShearRawSampleCertification

/-! ## IF-BS-22F-F8C30: executable rational coarse delta-net -/

structure RationalMeasurementRecord where
  nodeId : Nat
  measured : Rat
  instrumentNoise : Rat
  computationalResolution : Rat
  deriving Repr, DecidableEq

def RationalMeasurementRecord.accepted
    (record : RationalMeasurementRecord) : Bool :=
  record.nodeId == 0 &&
    record.measured == 1 &&
    record.instrumentNoise == 0 &&
    record.computationalResolution == 0

def rationalAxisDirection : AmbientPlane :=
  planeEmbedding ({ x := 1, y := 0 } : RealPlanePoint)

def rationalCoarseAnchor : BlowUpPoint :=
  (rationalAxisDirection, 0)

def coarseRationalRecord : RationalMeasurementRecord where
  nodeId := 0
  measured := 1
  instrumentNoise := 0
  computationalResolution := 0

def decodeRationalRecord
    (record : RationalMeasurementRecord) :
    NoisyUpperReading BlowUpPoint where
  point := rationalCoarseAnchor
  measured := (record.measured : ℝ)
  error :=
    ((record.instrumentNoise + record.computationalResolution : Rat) : ℝ)

def coarseRationalSample : List (NoisyUpperReading BlowUpPoint) :=
  [decodeRationalRecord coarseRationalRecord]

theorem coarseRationalRecord_accepted :
    coarseRationalRecord.accepted = true := by
  rfl

theorem rationalAxisDirection_mem_sphere :
    rationalAxisDirection ∈ Metric.sphere kernelOrigin 1 := by
  rw [Metric.mem_sphere, dist_comm]
  have hsq :=
    dist_sq_eq_coordinate_sq_sum kernelOrigin rationalAxisDirection
  simp [kernelOrigin, rationalAxisDirection, planeEmbedding] at hsq
  have hnonneg :
      0 ≤ dist kernelOrigin rationalAxisDirection := dist_nonneg
  rcases hsq with hpositive | hnegative
  · exact hpositive
  · have hnegative' :
        dist kernelOrigin rationalAxisDirection = -1 := by
      simpa [kernelOrigin, rationalAxisDirection, planeEmbedding] using
        hnegative
    nlinarith

theorem rationalCoarseAnchor_mem :
    rationalCoarseAnchor ∈ directionalDiamondBand := by
  rw [directionalDiamondBand, directionalBlowUpChamber]
  refine ⟨⟨rationalAxisDirection_mem_sphere, ?_⟩, ?_⟩
  · change (0 : ℝ) ∈ Set.Icc (-Real.sqrt 2) (Real.sqrt 2)
    constructor <;> nlinarith [sqrt_two_nonneg]
  · change |(0 : ℝ)| ≤
      |rationalAxisDirection.ofLp 0| + |rationalAxisDirection.ofLp 1|
    simp [rationalAxisDirection, planeEmbedding]

theorem forwardBlowUpSq_rationalCoarseAnchor
    (amplitude : ℝ) :
    forwardBlowUpSq amplitude rationalCoarseAnchor = 1 := by
  norm_num [forwardBlowUpSq, rationalCoarseAnchor,
    rationalAxisDirection, planeEmbedding]

theorem inverseBlowUpSq_rationalCoarseAnchor
    (amplitude : ℝ) :
    inverseBlowUpSq amplitude rationalCoarseAnchor = 1 := by
  rw [inverseBlowUpSq, forwardBlowUpSq_rationalCoarseAnchor]
  norm_num

theorem directionalDiamond_dist_rationalCoarseAnchor_le_two
    {point : BlowUpPoint} (hpoint : point ∈ directionalDiamondBand) :
    dist point rationalCoarseAnchor ≤ 2 := by
  rw [Prod.dist_eq]
  apply max_le
  · have hdir := hpoint.1.1
    rw [Metric.mem_sphere] at hdir
    have hanchor := rationalAxisDirection_mem_sphere
    rw [Metric.mem_sphere] at hanchor
    have htri :=
      dist_triangle point.1 kernelOrigin rationalAxisDirection
    have hanchor' : dist kernelOrigin rationalAxisDirection = 1 := by
      simpa [dist_comm] using hanchor
    simpa [rationalCoarseAnchor] using
      (show dist point.1 rationalAxisDirection ≤ 2 by
        nlinarith [htri])
  · have hslope : |point.2| ≤ Real.sqrt 2 :=
      abs_le.mpr hpoint.1.2
    have hsqrt : Real.sqrt 2 ≤ 2 := by
      nlinarith [sqrt_two_nonneg, sqrt_two_sq]
    rw [Real.dist_eq]
    simpa [rationalCoarseAnchor] using hslope.trans hsqrt

theorem coarseRationalSample_twoCoverage :
    DeltaCoverage directionalDiamondBand coarseRationalSample 2 := by
  intro point hpoint
  refine ⟨decodeRationalRecord coarseRationalRecord, ?_, ?_⟩
  · simp [coarseRationalSample]
  · simpa [decodeRationalRecord] using
      directionalDiamond_dist_rationalCoarseAnchor_le_two hpoint

theorem coarseRationalSample_inside :
    ∀ reading, reading ∈ coarseRationalSample →
      reading.point ∈ directionalDiamondBand := by
  intro reading hreading
  have heq : reading = decodeRationalRecord coarseRationalRecord := by
    simpa [coarseRationalSample] using hreading
  subst reading
  exact rationalCoarseAnchor_mem

theorem coarseForwardSplitBudgetValid
    (amplitude : ℝ) :
    SplitBudgetSampleValid
      (forwardBlowUpSq amplitude) coarseRationalSample 0 0 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro reading hreading
  have heq : reading = decodeRationalRecord coarseRationalRecord := by
    simpa [coarseRationalSample] using hreading
  subst reading
  constructor
  · norm_num [decodeRationalRecord, coarseRationalRecord]
  · simpa [decodeRationalRecord, coarseRationalRecord] using
      (show |(1 : ℝ) -
          forwardBlowUpSq amplitude rationalCoarseAnchor| ≤ 0 by
        rw [forwardBlowUpSq_rationalCoarseAnchor]
        norm_num)

theorem coarseInverseSplitBudgetValid
    (amplitude : ℝ) :
    SplitBudgetSampleValid
      (inverseBlowUpSq amplitude) coarseRationalSample 0 0 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro reading hreading
  have heq : reading = decodeRationalRecord coarseRationalRecord := by
    simpa [coarseRationalSample] using hreading
  subst reading
  constructor
  · norm_num [decodeRationalRecord, coarseRationalRecord]
  · simpa [decodeRationalRecord, coarseRationalRecord] using
      (show |(1 : ℝ) -
          inverseBlowUpSq amplitude rationalCoarseAnchor| ≤ 0 by
        rw [inverseBlowUpSq_rationalCoarseAnchor]
        norm_num)

theorem executableCoarseNet_certifies_noisy_reading
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    CertifiedNoisyMetricReading amplitude
      (rawMetricObserved coarseRationalSample
        (forwardBlowUpSqRegularity amplitude) 2)
      (rawMetricObserved coarseRationalSample
        (sharpDiamondInverseRegularity amplitude) 2)
      (rawMetricError coarseRationalSample
        (forwardBlowUpSqRegularity amplitude) 2)
      (rawMetricError coarseRationalSample
        (sharpDiamondInverseRegularity amplitude) 2) := by
  exact raw_finite_samples_certify_noisy_reading
    (amplitude := amplitude)
    (forwardDelta := 2) (inverseDelta := 2)
    (forwardInstrument := 0) (forwardResolution := 0)
    (inverseInstrument := 0) (inverseResolution := 0)
    ha0 ha1 (by norm_num) (by norm_num)
    (coarseForwardSplitBudgetValid amplitude)
    (coarseInverseSplitBudgetValid amplitude)
    coarseRationalSample_twoCoverage
    coarseRationalSample_twoCoverage
    coarseRationalSample_inside
    coarseRationalSample_inside

theorem executableCoarseNet_enters_F8C28_interval
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    amplitude ∈ Set.Icc
      (noisyAmplitudeLower
        (rawMetricObserved coarseRationalSample
          (forwardBlowUpSqRegularity amplitude) 2)
        (rawMetricError coarseRationalSample
          (forwardBlowUpSqRegularity amplitude) 2))
      (noisyAmplitudeUpper
        (rawMetricObserved coarseRationalSample
          (forwardBlowUpSqRegularity amplitude) 2)
        (rawMetricObserved coarseRationalSample
          (sharpDiamondInverseRegularity amplitude) 2)
        (rawMetricError coarseRationalSample
          (forwardBlowUpSqRegularity amplitude) 2)
        (rawMetricError coarseRationalSample
          (sharpDiamondInverseRegularity amplitude) 2)) :=
  certified_reading_amplitude_mem_interval
    (executableCoarseNet_certifies_noisy_reading ha0 ha1)

end

end BoundaryOfSelf.IntrinsicNonradialShearExecutableCoarseNet
