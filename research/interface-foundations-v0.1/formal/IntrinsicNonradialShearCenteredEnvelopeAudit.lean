import IntrinsicNonradialShearCenteredEnvelope

namespace BoundaryOfSelf.IntrinsicNonradialShearCenteredEnvelopeAudit

open IntrinsicNonradialShearTangentEnvelope
open IntrinsicNonradialShearCenteredEnvelope

theorem audited_centered_upper
    {amplitude X Y r k : ℝ}
    (ha0 : 0 ≤ amplitude)
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hr0 : 0 ≤ r) (hk0 : 0 ≤ k)
    (hXY : X ^ 2 + Y ^ 2 = 1)
    (hrk : r ^ 2 + k ^ 2 = 1) :
    centeredTwoPointEnvelope amplitude X Y r k ≤
      exactTangentEnvelope amplitude :=
  centeredTwoPointEnvelope_le_exact ha0 hX0 hY0 hr0 hk0 hXY hrk

theorem audited_centered_attainment
    {amplitude : ℝ}
    (ha0 : 0 ≤ amplitude) :
    centeredTwoPointEnvelope amplitude
        (tangentEnvelopePoint amplitude).1
        (tangentEnvelopePoint amplitude).2 1 0 =
      exactTangentEnvelope amplitude :=
  centeredTwoPointEnvelope_attains_exact ha0

theorem audited_centered_exact_optimum
    {amplitude : ℝ}
    (ha0 : 0 ≤ amplitude) :
    IsGreatest (CenteredEnvelopeValues amplitude)
      (exactTangentEnvelope amplitude) :=
  exactTangentEnvelope_isGreatest_centered ha0

#print axioms audited_centered_upper
#print axioms audited_centered_attainment
#print axioms audited_centered_exact_optimum

end BoundaryOfSelf.IntrinsicNonradialShearCenteredEnvelopeAudit

