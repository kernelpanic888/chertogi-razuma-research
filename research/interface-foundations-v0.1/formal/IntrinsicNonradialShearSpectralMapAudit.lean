import IntrinsicNonradialShearSpectralMap

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearSpectralMap

open StandardHausdorffMetricBridge
open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearKernelSharp

theorem audit_forward_global_upper
    {amplitude : ℝ} (ha : 0 ≤ amplitude)
    (first second : AmbientPlane) :
    dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second) ≤
      forwardSpectralConstant amplitude * dist first second :=
  intrinsicShearMap_dist_le_forwardSpectralConstant ha first second

theorem audit_forward_global_lower
    {amplitude constant : ℝ} (ha : 0 ≤ amplitude) (hc : 0 ≤ constant)
    (hbound : ForwardMapMetricBound amplitude constant) :
    forwardSpectralConstant amplitude ≤ constant :=
  forward_map_metric_bound_ge_spectralConstant ha hc hbound

theorem audit_forward_exact_threshold
    {amplitude constant : ℝ} (ha : 0 ≤ amplitude) (hc : 0 ≤ constant) :
    ForwardMapMetricBound amplitude constant ↔
      forwardSpectralConstant amplitude ≤ constant :=
  forward_map_metric_bound_iff ha hc

theorem audit_inverse_closed_form
    {amplitude : ℝ} (ha1 : amplitude < 1) :
    inverseSpectralSq amplitude =
      (1 - amplitude + amplitude ^ 2 +
        amplitude * Real.sqrt (amplitude ^ 2 - 2 * amplitude + 2)) /
          (1 - amplitude) ^ 2 :=
  inverseSpectralSq_closed_form ha1

theorem audit_backward_global_upper
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (ha1 : amplitude < 1)
    (first second : AmbientPlane) :
    dist first second ≤
      inverseSpectralConstant amplitude *
        dist (intrinsicShearMap amplitude first)
          (intrinsicShearMap amplitude second) :=
  intrinsicShearMap_colipschitz_inverseSpectralConstant
    ha ha1 first second

theorem audit_backward_global_lower
    {amplitude constant : ℝ}
    (ha : 0 ≤ amplitude) (ha1 : amplitude < 1) (hc : 0 ≤ constant)
    (hbound : BackwardMapMetricBound amplitude constant) :
    inverseSpectralConstant amplitude ≤ constant :=
  backward_map_metric_bound_ge_inverseSpectralConstant
    ha ha1 hc hbound

theorem audit_backward_exact_threshold
    {amplitude constant : ℝ}
    (ha : 0 ≤ amplitude) (ha1 : amplitude < 1) (hc : 0 ≤ constant) :
    BackwardMapMetricBound amplitude constant ↔
      inverseSpectralConstant amplitude ≤ constant :=
  backward_map_metric_bound_iff ha ha1 hc

#print axioms audit_forward_global_upper
#print axioms audit_forward_global_lower
#print axioms audit_forward_exact_threshold
#print axioms audit_inverse_closed_form
#print axioms audit_backward_global_upper
#print axioms audit_backward_global_lower
#print axioms audit_backward_exact_threshold

end BoundaryOfSelf.IntrinsicNonradialShearSpectralMap
