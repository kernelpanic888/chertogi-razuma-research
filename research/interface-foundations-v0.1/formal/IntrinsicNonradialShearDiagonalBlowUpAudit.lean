import IntrinsicNonradialShearDiagonalBlowUp

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearDiagonalBlowUp

open LocalSegmentRealCompletion
open StandardHausdorffMetricBridge
open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearDeltaNet
open IntrinsicNonradialShearClosedCore

theorem audit_blowUp_chamber_compact :
    IsCompact directionalBlowUpChamber :=
  directionalBlowUpChamber_compact

theorem audit_chord_enters_chamber
    {first second : AmbientPlane} (hne : first ≠ second) :
    chordBlowUp first second ∈ directionalBlowUpChamber :=
  chordBlowUp_mem_chamber hne

theorem audit_forward_sq_identity
    (amplitude : ℝ) {first second : AmbientPlane}
    (hne : first ≠ second) :
    dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second) ^ 2 =
      forwardBlowUpSq amplitude (chordBlowUp first second) *
        dist first second ^ 2 :=
  chordBlowUp_forward_sq_identity amplitude hne

theorem audit_explicit_regularity
    {amplitude : ℝ} (ha : 0 ≤ amplitude) :
    ∀ first ∈ directionalBlowUpChamber,
      ∀ second ∈ directionalBlowUpChamber,
        |forwardBlowUpSq amplitude first -
            forwardBlowUpSq amplitude second| ≤
          forwardBlowUpSqRegularity amplitude * dist first second :=
  forwardBlowUpSq_regularity_bound ha

theorem audit_finite_blowUp_certificate
    {amplitude delta : ℝ}
    (ha : 0 ≤ amplitude) (hdelta : 0 < delta) :
    ∃ sample : List (NoisyUpperReading BlowUpPoint),
      NoisyUpperSampleValid (forwardBlowUpSq amplitude) sample ∧
        DeltaCoverage directionalBlowUpChamber sample delta ∧
          SampleInside directionalBlowUpChamber sample ∧
            RegularityCertificate directionalBlowUpChamber sample
              (forwardBlowUpSqRegularity amplitude)
              (forwardBlowUpSq amplitude) ∧
              ∀ point, point ∈ directionalBlowUpChamber →
                forwardBlowUpSq amplitude point ≤
                  noisySampleUpper sample +
                    forwardBlowUpSqRegularity amplitude * delta :=
  exists_forwardBlowUpSq_finiteCertificate ha hdelta

theorem audit_chord_sq_transport
    {amplitude constant : ℝ}
    (hupper :
      ∀ point, point ∈ directionalBlowUpChamber →
        forwardBlowUpSq amplitude point ≤ constant)
    (first second : AmbientPlane) :
    dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second) ^ 2 ≤
      constant * dist first second ^ 2 :=
  chord_sq_bound_of_blowUp_upper hupper first second

theorem audit_finite_forward_chord_certificate
    {amplitude delta : ℝ}
    (ha : 0 ≤ amplitude) (hdelta : 0 < delta) :
    ∃ sample : List (NoisyUpperReading BlowUpPoint),
      NoisyUpperSampleValid (forwardBlowUpSq amplitude) sample ∧
        DeltaCoverage directionalBlowUpChamber sample delta ∧
          SampleInside directionalBlowUpChamber sample ∧
            RegularityCertificate directionalBlowUpChamber sample
              (forwardBlowUpSqRegularity amplitude)
              (forwardBlowUpSq amplitude) ∧
              ∀ first second : AmbientPlane,
                dist (intrinsicShearMap amplitude first)
                    (intrinsicShearMap amplitude second) ^ 2 ≤
                  (noisySampleUpper sample +
                    forwardBlowUpSqRegularity amplitude * delta) *
                    dist first second ^ 2 :=
  exists_finite_forwardChordSqCertificate ha hdelta

#print axioms audit_blowUp_chamber_compact
#print axioms audit_chord_enters_chamber
#print axioms audit_forward_sq_identity
#print axioms audit_explicit_regularity
#print axioms audit_finite_blowUp_certificate
#print axioms audit_chord_sq_transport
#print axioms audit_finite_forward_chord_certificate

end BoundaryOfSelf.IntrinsicNonradialShearDiagonalBlowUp
