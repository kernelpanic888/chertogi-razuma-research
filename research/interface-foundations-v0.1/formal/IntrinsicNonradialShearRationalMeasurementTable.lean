import IntrinsicNonradialShearStereographicMetricTransport

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearRationalMeasurementTable

noncomputable section

open StandardHausdorffMetricBridge
open IntrinsicNonradialShearDeltaNet
open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearDiagonalBlowUpInverse
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearRealizableCertificate
open IntrinsicNonradialShearSharpEnvelope
open IntrinsicNonradialShearNoisyIdentifiability
open IntrinsicNonradialShearRawSampleCertification
open IntrinsicNonradialShearRationalParameterRefinement
open IntrinsicNonradialShearStereographicDiamondLift
open IntrinsicNonradialShearStereographicMetricTransport

/-! ## IF-BS-22F-F8C31D: finite rational measurement-table materialization -/

def rationalChartSign (hemisphere : Bool) : Rat :=
  if hemisphere then 1 else -1

def rationalStereographicX (t : Rat) : Rat :=
  (1 - t ^ 2) / (1 + t ^ 2)

def rationalStereographicY (t : Rat) : Rat :=
  2 * t / (1 + t ^ 2)

def rationalDirectionX {level : Nat}
    (node : RationalParameterNode level) : Rat :=
  rationalChartSign node.hemisphere *
    rationalStereographicX node.serializedT

def rationalDirectionY {level : Nat}
    (node : RationalParameterNode level) : Rat :=
  rationalStereographicY node.serializedT

def rationalDirectionWidth {level : Nat}
    (node : RationalParameterNode level) : Rat :=
  |rationalDirectionX node| + |rationalDirectionY node|

def rationalSlope {level : Nat}
    (node : RationalParameterNode level) : Rat :=
  node.serializedV * rationalDirectionWidth node

def rationalForwardSq {level : Nat}
    (amplitude : Rat) (node : RationalParameterNode level) : Rat :=
  rationalDirectionX node ^ 2 +
    (rationalDirectionY node + amplitude * rationalSlope node) ^ 2

def rationalInverseSq {level : Nat}
    (amplitude : Rat) (node : RationalParameterNode level) : Rat :=
  (rationalForwardSq amplitude node)⁻¹

def rationalParameterNodeId {level : Nat}
    (node : RationalParameterNode level) : Nat :=
  (if node.hemisphere then 1 else 0) * (level + 2) ^ 2 +
    node.tIndex.val * (level + 2) + node.vIndex.val

/-- One self-describing exact row of the finite rational table. -/
structure ExactRationalMeasurementRecord (level : Nat) where
  nodeId : Nat
  node : RationalParameterNode level
  serializedT : Rat
  serializedV : Rat
  directionX : Rat
  directionY : Rat
  slope : Rat
  forwardMeasured : Rat
  inverseMeasured : Rat
  instrumentNoise : Rat
  computationalResolution : Rat
  deriving Repr, DecidableEq

def exactRationalMeasurementRecord {level : Nat}
    (amplitude : Rat) (node : RationalParameterNode level) :
    ExactRationalMeasurementRecord level where
  nodeId := rationalParameterNodeId node
  node := node
  serializedT := node.serializedT
  serializedV := node.serializedV
  directionX := rationalDirectionX node
  directionY := rationalDirectionY node
  slope := rationalSlope node
  forwardMeasured := rationalForwardSq amplitude node
  inverseMeasured := rationalInverseSq amplitude node
  instrumentNoise := 0
  computationalResolution := 0

def ExactRationalMeasurementRecord.accepted {level : Nat}
    (amplitude : Rat) (record : ExactRationalMeasurementRecord level) : Bool :=
  record.nodeId == rationalParameterNodeId record.node &&
  record.serializedT == record.node.serializedT &&
  record.serializedV == record.node.serializedV &&
  record.directionX == rationalDirectionX record.node &&
  record.directionY == rationalDirectionY record.node &&
  record.slope == rationalSlope record.node &&
  record.forwardMeasured == rationalForwardSq amplitude record.node &&
  record.inverseMeasured == rationalInverseSq amplitude record.node &&
  record.instrumentNoise == 0 &&
  record.computationalResolution == 0

theorem generated_record_accepted {level : Nat}
    (amplitude : Rat) (node : RationalParameterNode level) :
    (exactRationalMeasurementRecord amplitude node).accepted amplitude = true := by
  simp [ExactRationalMeasurementRecord.accepted,
    exactRationalMeasurementRecord]

/-- Deterministic enumeration of every node at one refinement level. -/
noncomputable def rationalMeasurementTable
    (level : Nat) (amplitude : Rat) :
    List (ExactRationalMeasurementRecord level) :=
  (Finset.univ : Finset (RationalParameterNode level)).toList.map
    (exactRationalMeasurementRecord amplitude)

theorem rationalMeasurementTable_length
    (level : Nat) (amplitude : Rat) :
    (rationalMeasurementTable level amplitude).length =
      Fintype.card (RationalParameterNode level) := by
  simp [rationalMeasurementTable]

theorem generated_record_mem_table {level : Nat}
    (amplitude : Rat) (node : RationalParameterNode level) :
    exactRationalMeasurementRecord amplitude node ∈
      rationalMeasurementTable level amplitude := by
  simp [rationalMeasurementTable]

lemma rationalChartSign_cast (hemisphere : Bool) :
    ((rationalChartSign hemisphere : Rat) : ℝ) =
      chartSign hemisphere := by
  cases hemisphere <;> simp [rationalChartSign, chartSign]

lemma rationalStereographicX_cast (t : Rat) :
    ((rationalStereographicX t : Rat) : ℝ) =
      stereographicX (t : ℝ) := by
  norm_num [rationalStereographicX, stereographicX]

lemma rationalStereographicY_cast (t : Rat) :
    ((rationalStereographicY t : Rat) : ℝ) =
      stereographicY (t : ℝ) := by
  norm_num [rationalStereographicY, stereographicY]

lemma serializedT_cast {level : Nat}
    (node : RationalParameterNode level) :
    ((node.serializedT : Rat) : ℝ) = node.t := by
  exact rationalGridValue_cast level node.tIndex

lemma serializedV_cast {level : Nat}
    (node : RationalParameterNode level) :
    ((node.serializedV : Rat) : ℝ) = node.v := by
  exact rationalGridValue_cast level node.vIndex

lemma rationalDirectionX_cast {level : Nat}
    (node : RationalParameterNode level) :
    ((rationalDirectionX node : Rat) : ℝ) =
      (stereographicDirection node.hemisphere node.t).ofLp 0 := by
  rw [stereographicDirection_zero]
  simp [rationalDirectionX, rationalChartSign_cast,
    rationalStereographicX_cast, serializedT_cast]

lemma rationalDirectionY_cast {level : Nat}
    (node : RationalParameterNode level) :
    ((rationalDirectionY node : Rat) : ℝ) =
      (stereographicDirection node.hemisphere node.t).ofLp 1 := by
  rw [stereographicDirection_one]
  simp [rationalDirectionY, rationalStereographicY_cast,
    serializedT_cast]

lemma rationalDirectionWidth_cast {level : Nat}
    (node : RationalParameterNode level) :
    ((rationalDirectionWidth node : Rat) : ℝ) =
      stereographicWidth node.hemisphere node.t := by
  simp [rationalDirectionWidth, stereographicWidth,
    rationalDirectionX_cast, rationalDirectionY_cast]

lemma rationalSlope_cast {level : Nat}
    (node : RationalParameterNode level) :
    ((rationalSlope node : Rat) : ℝ) =
      (liftedRationalNode node).2 := by
  simp [rationalSlope, liftedRationalNode, stereographicDiamondLift,
    serializedV_cast, rationalDirectionWidth_cast]

lemma rationalForwardSq_cast {level : Nat}
    (amplitude : Rat) (node : RationalParameterNode level) :
    ((rationalForwardSq amplitude node : Rat) : ℝ) =
      forwardBlowUpSq (amplitude : ℝ) (liftedRationalNode node) := by
  simp [rationalForwardSq, forwardBlowUpSq, liftedRationalNode,
    stereographicDiamondLift, rationalDirectionX_cast,
    rationalDirectionY_cast, rationalSlope_cast]

lemma rationalInverseSq_cast {level : Nat}
    (amplitude : Rat) (node : RationalParameterNode level) :
    ((rationalInverseSq amplitude node : Rat) : ℝ) =
      inverseBlowUpSq (amplitude : ℝ) (liftedRationalNode node) := by
  simp [rationalInverseSq, inverseBlowUpSq, rationalForwardSq_cast]

def decodeForwardRecord {level : Nat}
    (record : ExactRationalMeasurementRecord level) :
    NoisyUpperReading BlowUpPoint where
  point := liftedRationalNode record.node
  measured := (record.forwardMeasured : ℝ)
  error := ((record.instrumentNoise +
    record.computationalResolution : Rat) : ℝ)

def decodeInverseRecord {level : Nat}
    (record : ExactRationalMeasurementRecord level) :
    NoisyUpperReading BlowUpPoint where
  point := liftedRationalNode record.node
  measured := (record.inverseMeasured : ℝ)
  error := ((record.instrumentNoise +
    record.computationalResolution : Rat) : ℝ)

noncomputable def forwardRationalSample
    (level : Nat) (amplitude : Rat) :
    List (NoisyUpperReading BlowUpPoint) :=
  (rationalMeasurementTable level amplitude).map decodeForwardRecord

noncomputable def inverseRationalSample
    (level : Nat) (amplitude : Rat) :
    List (NoisyUpperReading BlowUpPoint) :=
  (rationalMeasurementTable level amplitude).map decodeInverseRecord

lemma generated_forward_reading_mem {level : Nat}
    (amplitude : Rat) (node : RationalParameterNode level) :
    decodeForwardRecord (exactRationalMeasurementRecord amplitude node) ∈
      forwardRationalSample level amplitude := by
  simp [forwardRationalSample, rationalMeasurementTable]

lemma generated_inverse_reading_mem {level : Nat}
    (amplitude : Rat) (node : RationalParameterNode level) :
    decodeInverseRecord (exactRationalMeasurementRecord amplitude node) ∈
      inverseRationalSample level amplitude := by
  simp [inverseRationalSample, rationalMeasurementTable]

theorem forwardRationalSample_coverage
    (level : Nat) (amplitude : Rat) :
    DeltaCoverage directionalDiamondBand
      (forwardRationalSample level amplitude)
      (exactDiamondMeshRadius level) := by
  intro point hpoint
  obtain ⟨node, hclose⟩ :=
    exists_liftedRationalNode_close level point hpoint
  refine ⟨decodeForwardRecord
    (exactRationalMeasurementRecord amplitude node),
      generated_forward_reading_mem amplitude node, ?_⟩
  simpa [decodeForwardRecord, exactRationalMeasurementRecord] using hclose

theorem inverseRationalSample_coverage
    (level : Nat) (amplitude : Rat) :
    DeltaCoverage directionalDiamondBand
      (inverseRationalSample level amplitude)
      (exactDiamondMeshRadius level) := by
  intro point hpoint
  obtain ⟨node, hclose⟩ :=
    exists_liftedRationalNode_close level point hpoint
  refine ⟨decodeInverseRecord
    (exactRationalMeasurementRecord amplitude node),
      generated_inverse_reading_mem amplitude node, ?_⟩
  simpa [decodeInverseRecord, exactRationalMeasurementRecord] using hclose

theorem forwardRationalSample_inside
    (level : Nat) (amplitude : Rat) :
    ∀ reading, reading ∈ forwardRationalSample level amplitude →
      reading.point ∈ directionalDiamondBand := by
  intro reading hreading
  rw [forwardRationalSample] at hreading
  obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp hreading
  rw [rationalMeasurementTable] at hrecord
  obtain ⟨node, _, rfl⟩ := List.mem_map.mp hrecord
  exact liftedRationalNode_mem_exactDiamond node

theorem inverseRationalSample_inside
    (level : Nat) (amplitude : Rat) :
    ∀ reading, reading ∈ inverseRationalSample level amplitude →
      reading.point ∈ directionalDiamondBand := by
  intro reading hreading
  rw [inverseRationalSample] at hreading
  obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp hreading
  rw [rationalMeasurementTable] at hrecord
  obtain ⟨node, _, rfl⟩ := List.mem_map.mp hrecord
  exact liftedRationalNode_mem_exactDiamond node

theorem forwardRationalSample_splitBudgetValid
    (level : Nat) (amplitude : Rat) :
    SplitBudgetSampleValid (forwardBlowUpSq (amplitude : ℝ))
      (forwardRationalSample level amplitude) 0 0 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro reading hreading
  rw [forwardRationalSample] at hreading
  obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp hreading
  rw [rationalMeasurementTable] at hrecord
  obtain ⟨node, _, rfl⟩ := List.mem_map.mp hrecord
  constructor
  · norm_num [decodeForwardRecord, exactRationalMeasurementRecord]
  · simp [decodeForwardRecord, exactRationalMeasurementRecord,
      rationalForwardSq_cast]

theorem inverseRationalSample_splitBudgetValid
    (level : Nat) (amplitude : Rat) :
    SplitBudgetSampleValid (inverseBlowUpSq (amplitude : ℝ))
      (inverseRationalSample level amplitude) 0 0 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro reading hreading
  rw [inverseRationalSample] at hreading
  obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp hreading
  rw [rationalMeasurementTable] at hrecord
  obtain ⟨node, _, rfl⟩ := List.mem_map.mp hrecord
  constructor
  · norm_num [decodeInverseRecord, exactRationalMeasurementRecord]
  · simp [decodeInverseRecord, exactRationalMeasurementRecord,
      rationalInverseSq_cast]

private lemma exactDiamondMeshRadius_nonnegative (level : Nat) :
    0 ≤ exactDiamondMeshRadius level := by
  exact mul_nonneg (by norm_num)
    (parameterMeshRadius_nonnegative level)

/-- The materialized table enters the existing F8C29 certificate pipeline. -/
theorem rationalMeasurementTable_certifies_noisy_reading
    (level : Nat) {amplitude : Rat}
    (ha0 : 0 ≤ (amplitude : ℝ)) (ha1 : (amplitude : ℝ) < 1) :
    CertifiedNoisyMetricReading (amplitude : ℝ)
      (rawMetricObserved (forwardRationalSample level amplitude)
        (forwardBlowUpSqRegularity (amplitude : ℝ))
        (exactDiamondMeshRadius level))
      (rawMetricObserved (inverseRationalSample level amplitude)
        (sharpDiamondInverseRegularity (amplitude : ℝ))
        (exactDiamondMeshRadius level))
      (rawMetricError (forwardRationalSample level amplitude)
        (forwardBlowUpSqRegularity (amplitude : ℝ))
        (exactDiamondMeshRadius level))
      (rawMetricError (inverseRationalSample level amplitude)
        (sharpDiamondInverseRegularity (amplitude : ℝ))
        (exactDiamondMeshRadius level)) := by
  exact raw_finite_samples_certify_noisy_reading
    (amplitude := (amplitude : ℝ))
    (forwardDelta := exactDiamondMeshRadius level)
    (inverseDelta := exactDiamondMeshRadius level)
    (forwardInstrument := 0) (forwardResolution := 0)
    (inverseInstrument := 0) (inverseResolution := 0)
    ha0 ha1 (exactDiamondMeshRadius_nonnegative level)
    (exactDiamondMeshRadius_nonnegative level)
    (forwardRationalSample_splitBudgetValid level amplitude)
    (inverseRationalSample_splitBudgetValid level amplitude)
    (forwardRationalSample_coverage level amplitude)
    (inverseRationalSample_coverage level amplitude)
    (forwardRationalSample_inside level amplitude)
    (inverseRationalSample_inside level amplitude)

/-- The same materialized table reaches the F8C28 amplitude interval. -/
theorem rationalMeasurementTable_enters_F8C28_interval
    (level : Nat) {amplitude : Rat}
    (ha0 : 0 ≤ (amplitude : ℝ)) (ha1 : (amplitude : ℝ) < 1) :
    (amplitude : ℝ) ∈ Set.Icc
      (noisyAmplitudeLower
        (rawMetricObserved (forwardRationalSample level amplitude)
          (forwardBlowUpSqRegularity (amplitude : ℝ))
          (exactDiamondMeshRadius level))
        (rawMetricError (forwardRationalSample level amplitude)
          (forwardBlowUpSqRegularity (amplitude : ℝ))
          (exactDiamondMeshRadius level)))
      (noisyAmplitudeUpper
        (rawMetricObserved (forwardRationalSample level amplitude)
          (forwardBlowUpSqRegularity (amplitude : ℝ))
          (exactDiamondMeshRadius level))
        (rawMetricObserved (inverseRationalSample level amplitude)
          (sharpDiamondInverseRegularity (amplitude : ℝ))
          (exactDiamondMeshRadius level))
        (rawMetricError (forwardRationalSample level amplitude)
          (forwardBlowUpSqRegularity (amplitude : ℝ))
          (exactDiamondMeshRadius level))
        (rawMetricError (inverseRationalSample level amplitude)
          (sharpDiamondInverseRegularity (amplitude : ℝ))
          (exactDiamondMeshRadius level))) :=
  certified_reading_amplitude_mem_interval
    (rationalMeasurementTable_certifies_noisy_reading level ha0 ha1)

end

end BoundaryOfSelf.IntrinsicNonradialShearRationalMeasurementTable
