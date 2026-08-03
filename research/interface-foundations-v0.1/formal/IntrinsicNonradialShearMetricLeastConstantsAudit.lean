import IntrinsicNonradialShearMetricLeastConstants

namespace BoundaryOfSelf.IntrinsicNonradialShearMetricLeastConstantsAudit

open IntrinsicNonradialShearSharpEnvelope
open IntrinsicNonradialShearKernelSharp
open IntrinsicNonradialShearSpectralMap
open IntrinsicNonradialShearMetricLeastConstants

theorem audited_upper_square_bridge (amplitude : ℝ) :
    exactDiamondUpperSq amplitude = forwardSpectralSq amplitude :=
  exactDiamondUpperSq_eq_forwardSpectralSq amplitude

theorem audited_lower_inverse_bridge
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    exactDiamondLowerSq amplitude * inverseSpectralSq amplitude = 1 :=
  exactDiamondLowerSq_mul_inverseSpectralSq ha0 ha1

theorem audited_direct_least
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    IsLeast (ForwardNonnegativeMetricModuli amplitude)
      (exactDirectMetricConstant amplitude) :=
  exactDirectMetricConstant_isLeast ha0

theorem audited_inverse_least
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    IsLeast (BackwardNonnegativeMetricModuli amplitude)
      (exactInverseMetricConstant amplitude) :=
  exactInverseMetricConstant_isLeast ha0 ha1

theorem audited_simultaneous_least
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    IsLeast (ForwardNonnegativeMetricModuli amplitude)
        (exactDirectMetricConstant amplitude) ∧
      IsLeast (BackwardNonnegativeMetricModuli amplitude)
        (exactInverseMetricConstant amplitude) :=
  exactMetricConstants_areSimultaneouslyLeast ha0 ha1

#print axioms audited_upper_square_bridge
#print axioms audited_lower_inverse_bridge
#print axioms audited_direct_least
#print axioms audited_inverse_least
#print axioms audited_simultaneous_least

end BoundaryOfSelf.IntrinsicNonradialShearMetricLeastConstantsAudit
