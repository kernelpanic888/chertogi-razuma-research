import IntrinsicNonradialShearExecutableCoarseNet

namespace BoundaryOfSelf.IntrinsicNonradialShearExecutableCoarseNetAudit

open Set
open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearDiagonalBlowUpInverse
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearDeltaNet
open IntrinsicNonradialShearSharpEnvelope
open IntrinsicNonradialShearNoisyIdentifiability
open IntrinsicNonradialShearRawSampleCertification
open IntrinsicNonradialShearExecutableCoarseNet

theorem audited_anchor_inside :
    rationalCoarseAnchor ∈ directionalDiamondBand :=
  rationalCoarseAnchor_mem

theorem audited_two_coverage :
    DeltaCoverage directionalDiamondBand coarseRationalSample 2 :=
  coarseRationalSample_twoCoverage

theorem audited_executable_record :
    coarseRationalRecord.accepted = true :=
  coarseRationalRecord_accepted

theorem audited_coarse_pipeline
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    CertifiedNoisyMetricReading amplitude
      (rawMetricObserved coarseRationalSample
        (forwardBlowUpSqRegularity amplitude) 2)
      (rawMetricObserved coarseRationalSample
        (sharpDiamondInverseRegularity amplitude) 2)
      (rawMetricError coarseRationalSample
        (forwardBlowUpSqRegularity amplitude) 2)
      (rawMetricError coarseRationalSample
        (sharpDiamondInverseRegularity amplitude) 2) :=
  executableCoarseNet_certifies_noisy_reading ha0 ha1

theorem audited_interval_entry
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
  executableCoarseNet_enters_F8C28_interval ha0 ha1

#print axioms audited_anchor_inside
#print axioms audited_two_coverage
#print axioms audited_executable_record
#print axioms audited_coarse_pipeline
#print axioms audited_interval_entry

end BoundaryOfSelf.IntrinsicNonradialShearExecutableCoarseNetAudit
