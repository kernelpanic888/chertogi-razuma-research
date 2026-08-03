import IntrinsicNonradialShearKernelSharp

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearKernelSharp

open StandardHausdorffMetricBridge
open IntrinsicNonradialShearLimit

theorem audit_diagonal_kernel_difference
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |shearKernel kernelOrigin - shearKernel (kernelDiagonalPoint t)| =
      t * (2 - t) := by
  rw [shearKernel_kernelOrigin]
  rw [shearKernel_kernelDiagonalPoint ht0 ht1]
  have hnonneg : 0 ≤ 1 - (1 - t) ^ 2 := by nlinarith
  rw [abs_of_nonneg hnonneg]
  ring

theorem audit_sqrt_two_upper :
    KernelMetricBound (Real.sqrt 2) :=
  sqrt_two_is_kernel_metric_bound

theorem audit_sqrt_two_lower
    {constant : ℝ} (hc0 : 0 ≤ constant)
    (hbound : KernelMetricBound constant) :
    Real.sqrt 2 ≤ constant := by
  exact kernel_metric_bound_ge_sqrt_two hc0 hbound

theorem audit_kernel_exact_threshold
    {constant : ℝ} (hc0 : 0 ≤ constant) :
    KernelMetricBound constant ↔ Real.sqrt 2 ≤ constant :=
  kernel_metric_bound_iff hc0

theorem audit_forward_spectral_upper
    {amplitude : ℝ} (ha : 0 ≤ amplitude) :
    ForwardQuadraticBound amplitude (forwardSpectralSq amplitude) :=
  forward_spectral_sq_is_quadratic_bound ha

theorem audit_forward_spectral_lower
    {amplitude constant : ℝ} (ha : 0 ≤ amplitude)
    (hbound : ForwardQuadraticBound amplitude constant) :
    forwardSpectralSq amplitude ≤ constant :=
  forward_quadratic_bound_ge_spectral_sq ha hbound

theorem audit_forward_spectral_exact_threshold
    {amplitude constant : ℝ} (ha : 0 ≤ amplitude) :
    ForwardQuadraticBound amplitude constant ↔
      forwardSpectralSq amplitude ≤ constant :=
  forward_quadratic_bound_iff ha

#print axioms audit_diagonal_kernel_difference
#print axioms audit_sqrt_two_upper
#print axioms audit_sqrt_two_lower
#print axioms audit_kernel_exact_threshold
#print axioms audit_forward_spectral_upper
#print axioms audit_forward_spectral_lower
#print axioms audit_forward_spectral_exact_threshold

end BoundaryOfSelf.IntrinsicNonradialShearKernelSharp
