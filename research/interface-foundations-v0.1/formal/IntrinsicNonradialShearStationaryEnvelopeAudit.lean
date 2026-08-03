import IntrinsicNonradialShearStationaryEnvelope

namespace BoundaryOfSelf.IntrinsicNonradialShearStationaryEnvelope

noncomputable section

open IntrinsicNonradialShearTangentEnvelope

def audit_stationary_monotone (amplitude : ℝ) (ha0 : 0 ≤ amplitude) :=
  slopeStationaryBalance_strictMonoOn ha0
def audit_unique_root (amplitude : ℝ) (ha0 : 0 ≤ amplitude) :=
  existsUnique_slopeStationaryRoot ha0
def audit_unique_profile_max
    (amplitude t : ℝ) (ha0 : 0 ≤ amplitude) (ht : t ∈ Set.Icc 0 1)
    (heq : slopeEnvelopeProfile amplitude t =
      slopeEnvelopeProfile amplitude (slopeCriticalPoint amplitude)) :=
  slopeEnvelopeProfile_unique_max ha0 ht heq
def audit_profile_global_upper
    (amplitude : ℝ) (ha0 : 0 ≤ amplitude) (coordinates : ℝ × ℝ)
    (hcoordinates : coordinates ∈ (FirstQuadrantUnit : Set (ℝ × ℝ))) :=
  scalarTangentDensity_le_criticalProfile ha0 hcoordinates
def audit_exact_envelope (amplitude : ℝ) (ha0 : 0 ≤ amplitude) :=
  exactTangentEnvelope_eq_criticalProfile ha0
def audit_half_polynomial := halfAmplitudeCriticalPoint_polynomial
def audit_half_bracket := halfAmplitudeCriticalPoint_bracket
def audit_half_certificate := halfAmplitudeEnvelopeValue_certificate
def audit_half_exact_modulus := halfAmplitude_exactLocalTangentModulus

#print axioms audit_stationary_monotone
#print axioms audit_unique_root
#print axioms audit_unique_profile_max
#print axioms audit_profile_global_upper
#print axioms audit_exact_envelope
#print axioms audit_half_polynomial
#print axioms audit_half_bracket
#print axioms audit_half_certificate
#print axioms audit_half_exact_modulus

end


end BoundaryOfSelf.IntrinsicNonradialShearStationaryEnvelope
