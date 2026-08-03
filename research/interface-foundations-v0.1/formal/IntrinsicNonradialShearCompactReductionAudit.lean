import IntrinsicNonradialShearCompactReduction

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearCompactReduction

open LocalSegmentRealCompletion
open StandardHausdorffMetricBridge
open CompactTentHomeomorphism
open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearExactSupport
open IntrinsicNonradialShearSpectralMap

theorem audit_point_displacement
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (point : AmbientPlane) :
    dist (intrinsicShearMap amplitude point) point ≤ amplitude :=
  intrinsicShearMap_displacement_le ha point

theorem audit_outside_carrier_identity
    (amplitude : ℝ) {first second : AmbientPlane}
    (hfirst : first ∉ intrinsicShearExactCarrier)
    (hsecond : second ∉ intrinsicShearExactCarrier) :
    dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second) = dist first second :=
  outsideCarrier_pair_is_fixed amplitude hfirst hsecond

theorem audit_forward_far_field
    {amplitude separation : ℝ} {first second : AmbientPlane}
    (ha : 0 ≤ amplitude) (hseparation : 0 < separation)
    (hlong : separation ≤ dist first second) :
    dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second) ≤
      (1 + 2 * amplitude / separation) * dist first second :=
  longChord_forward_bound ha hseparation hlong

theorem audit_backward_far_field
    {amplitude separation : ℝ} {first second : AmbientPlane}
    (ha : 0 ≤ amplitude) (hseparation : 0 < separation)
    (hlong :
      separation ≤
        dist (intrinsicShearMap amplitude first)
          (intrinsicShearMap amplitude second)) :
    dist first second ≤
      (1 + 2 * amplitude / separation) *
        dist (intrinsicShearMap amplitude first)
          (intrinsicShearMap amplitude second) :=
  longChord_backward_bound ha hseparation hlong

theorem audit_forward_core_container
    {separation : ℝ} (hseparation : 0 ≤ separation) :
    ActiveShortChordCore separation ⊆
      compactChordBox (Real.sqrt 2 + separation) :=
  activeShortChordCore_subset_compactBox hseparation

theorem audit_backward_core_container
    {amplitude separation : ℝ}
    (ha : 0 ≤ amplitude) (hseparation : 0 ≤ separation) :
    ActiveOutputShortChordCore amplitude separation ⊆
      compactChordBox (Real.sqrt 2 + separation + 2 * amplitude) :=
  activeOutputShortChordCore_subset_compactBox ha hseparation

theorem audit_forward_global_reduction
    {amplitude separation coreUpper : ℝ}
    (ha : 0 ≤ amplitude) (hseparation : 0 < separation)
    (hcoreUpper : 0 ≤ coreUpper)
    (hcore :
      ∀ pair ∈ ActiveShortChordCore separation,
        dist (intrinsicShearMap amplitude pair.1)
            (intrinsicShearMap amplitude pair.2) ≤
          coreUpper * dist pair.1 pair.2) :
    ForwardMapMetricBound amplitude
      (max 1 (max (1 + 2 * amplitude / separation) coreUpper)) :=
  forward_global_bound_of_compactCore ha hseparation hcoreUpper hcore

theorem audit_backward_global_reduction
    {amplitude separation coreUpper : ℝ}
    (ha : 0 ≤ amplitude) (hseparation : 0 < separation)
    (hcoreUpper : 0 ≤ coreUpper)
    (hcore :
      ∀ pair ∈ ActiveOutputShortChordCore amplitude separation,
        dist pair.1 pair.2 ≤
          coreUpper *
            dist (intrinsicShearMap amplitude pair.1)
              (intrinsicShearMap amplitude pair.2)) :
    BackwardMapMetricBound amplitude
      (max 1 (max (1 + 2 * amplitude / separation) coreUpper)) :=
  backward_global_bound_of_compactCore ha hseparation hcoreUpper hcore

#print axioms audit_point_displacement
#print axioms audit_outside_carrier_identity
#print axioms audit_forward_far_field
#print axioms audit_backward_far_field
#print axioms audit_forward_core_container
#print axioms audit_backward_core_container
#print axioms audit_forward_global_reduction
#print axioms audit_backward_global_reduction

end BoundaryOfSelf.IntrinsicNonradialShearCompactReduction
