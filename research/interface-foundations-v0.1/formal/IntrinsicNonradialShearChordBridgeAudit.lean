import IntrinsicNonradialShearChordBridge

namespace BoundaryOfSelf.IntrinsicNonradialShearChordBridgeAudit

open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearTangentEnvelope
open IntrinsicNonradialShearStationaryEnvelope
open IntrinsicNonradialShearChordBridge

theorem audited_forward_pair
    {amplitude : ℝ}
    (ha0 : 0 ≤ amplitude)
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand) :
    |forwardBlowUpSq amplitude first - forwardBlowUpSq amplitude second| ≤
      chordBridgeModulus amplitude * dist first second :=
  forwardBlowUpSq_chord_bridge ha0 hfirst hsecond

theorem audited_local_to_chord
    {amplitude : ℝ}
    (ha0 : 0 ≤ amplitude) :
    exactLocalTangentModulus amplitude ≤ chordBridgeModulus amplitude :=
  exactLocalTangentModulus_le_chordBridgeModulus ha0

theorem audited_half_amplitude :
    exactLocalTangentModulus (1 / 2 : ℝ) = halfAmplitudeEnvelopeValue ∧
      chordBridgeModulus (1 / 2 : ℝ) =
        1 + (3 / 2 : ℝ) * Real.sqrt 2 ∧
      0 ≤ chordBridgeGap (1 / 2 : ℝ) :=
  halfAmplitude_chordBridge_certificate

#print axioms audited_forward_pair
#print axioms audited_local_to_chord
#print axioms audited_half_amplitude

end BoundaryOfSelf.IntrinsicNonradialShearChordBridgeAudit

