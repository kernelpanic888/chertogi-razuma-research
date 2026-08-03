import IntrinsicNonradialShearExactSupport

open Set Filter Metric Topology

namespace BoundaryOfSelf.IntrinsicNonradialShearExactSupportAudit

open BoundaryOfSelf.StandardHausdorffMetricBridge
open BoundaryOfSelf.IntrinsicNonradialShearLimit
open BoundaryOfSelf.IntrinsicNonradialShearExactSupport

theorem audit_exact_moving_closure
    (amplitude : ℝ) (hAmplitude : 0 < amplitude) :
    closure (intrinsicShearMovingSet amplitude) =
      intrinsicShearExactCarrier :=
  closure_intrinsicShearMovingSet amplitude hAmplitude

theorem audit_square_frontier :
    frontier intrinsicShearExactCarrier =
      intrinsicShearSquarePerimeter :=
  frontier_intrinsicShearExactCarrier

theorem audit_minimal_closed_carrier
    (amplitude : ℝ) (hAmplitude : 0 < amplitude)
    {carrier : Set AmbientPlane} (hClosed : _root_.IsClosed carrier)
    (hOutside : ∀ point, point ∉ carrier →
      intrinsicShearMap amplitude point = point) :
    intrinsicShearExactCarrier ⊆ carrier :=
  intrinsicShearExactCarrier_minimal amplitude hAmplitude hClosed hOutside

theorem audit_forward_sqrt_two
    (amplitude : ℝ) (hAmplitude : 0 ≤ amplitude)
    (first second : AmbientPlane) :
    dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second) ≤
      (1 + Real.sqrt 2 * amplitude) * dist first second :=
  intrinsicShearMap_dist_le_sqrt_two amplitude hAmplitude first second

theorem audit_inverse_gap
    (amplitude : ℝ) (hAmplitude : 0 ≤ amplitude)
    (hQuarter : amplitude ≤ 1 / 4)
    (first second : AmbientPlane) :
    dist ((intrinsicShearEquiv amplitude hAmplitude hQuarter).symm first)
        ((intrinsicShearEquiv amplitude hAmplitude hQuarter).symm second) ≤
      (1 / (1 - Real.sqrt 2 * amplitude)) * dist first second :=
  intrinsicShearEquiv_inverse_dist_le_sqrt_two
    amplitude hAmplitude hQuarter first second

theorem audit_axis_forward_lower_bound
    (amplitude constant : ℝ) (hAmplitude : 0 ≤ amplitude)
    (hBound : ∀ first second,
      dist (intrinsicShearMap amplitude first)
          (intrinsicShearMap amplitude second) ≤
        constant * dist first second) :
    1 + amplitude ≤ constant :=
  forward_constant_ge_one_add_amplitude
    amplitude constant hAmplitude hBound

theorem audit_axis_inverse_lower_bound
    (amplitude constant : ℝ) (hBelowOne : amplitude < 1)
    (hBound : ∀ first second,
      dist first second ≤ constant *
        dist (intrinsicShearMap amplitude first)
          (intrinsicShearMap amplitude second)) :
    1 / (1 - amplitude) ≤ constant :=
  inverse_constant_ge_inv_one_sub_amplitude
    amplitude constant hBelowOne hBound

#print axioms audit_exact_moving_closure
#print axioms audit_square_frontier
#print axioms audit_minimal_closed_carrier
#print axioms audit_forward_sqrt_two
#print axioms audit_inverse_gap
#print axioms audit_axis_forward_lower_bound
#print axioms audit_axis_inverse_lower_bound

end BoundaryOfSelf.IntrinsicNonradialShearExactSupportAudit
