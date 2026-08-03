import IntrinsicNonradialShearClosedCore

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearClosedCore

open LocalSegmentRealCompletion
open StandardHausdorffMetricBridge
open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearExactSupport
open IntrinsicNonradialShearDeltaNet
open IntrinsicNonradialShearCompactReduction

theorem audit_forward_core_closed (separation : ℝ) :
    _root_.IsClosed (ActiveShortChordCore separation) :=
  activeShortChordCore_closed separation

theorem audit_backward_core_closed
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (separation : ℝ) :
    _root_.IsClosed (ActiveOutputShortChordCore amplitude separation) :=
  activeOutputShortChordCore_closed ha separation

theorem audit_forward_core_compact
    {separation : ℝ} (hseparation : 0 ≤ separation) :
    IsCompact (ActiveShortChordCore separation) :=
  activeShortChordCore_compact hseparation

theorem audit_backward_core_compact
    {amplitude separation : ℝ}
    (ha : 0 ≤ amplitude) (hseparation : 0 ≤ separation) :
    IsCompact (ActiveOutputShortChordCore amplitude separation) :=
  activeOutputShortChordCore_compact ha hseparation

theorem audit_finite_delta_net
    {α : Type*} [PseudoMetricSpace α]
    {domain : Set α} (hcompact : IsCompact domain)
    {delta : ℝ} (hdelta : 0 < delta) :
    FiniteMetricDeltaNet domain delta :=
  finiteMetricDeltaNet_of_compact hcompact hdelta

theorem audit_finite_exact_sample
    {α : Type*} [PseudoMetricSpace α]
    {domain : Set α} (hcompact : IsCompact domain)
    {delta : ℝ} (hdelta : 0 < delta) (value : α → ℝ) :
    ∃ sample : List (NoisyUpperReading α),
      NoisyUpperSampleValid value sample ∧
        DeltaCoverage domain sample delta ∧
          SampleInside domain sample :=
  compact_exists_finite_exactSample hcompact hdelta value

theorem audit_finite_global_certificate
    {α : Type*} [PseudoMetricSpace α]
    {domain : Set α} (hcompact : IsCompact domain)
    {delta : ℝ} (hdelta : 0 < delta) (value : α → ℝ) :
    ∃ sample : List (NoisyUpperReading α),
      NoisyUpperSampleValid value sample ∧
        DeltaCoverage domain sample delta ∧
          SampleInside domain sample ∧
            ∀ {constant : ℝ}, 0 ≤ constant →
              RegularityCertificate domain sample constant value →
                ∀ point, point ∈ domain →
                  value point ≤
                    noisySampleUpper sample + constant * delta :=
  compact_exists_finite_globalCertificate hcompact hdelta value

theorem audit_forward_core_sample
    {separation delta : ℝ}
    (hseparation : 0 ≤ separation) (hdelta : 0 < delta)
    (value : (AmbientPlane × AmbientPlane) → ℝ) :
    ∃ sample : List (NoisyUpperReading (AmbientPlane × AmbientPlane)),
      NoisyUpperSampleValid value sample ∧
        DeltaCoverage (ActiveShortChordCore separation) sample delta ∧
          SampleInside (ActiveShortChordCore separation) sample :=
  forwardCore_exists_finite_exactSample hseparation hdelta value

theorem audit_backward_core_sample
    {amplitude separation delta : ℝ}
    (ha : 0 ≤ amplitude) (hseparation : 0 ≤ separation)
    (hdelta : 0 < delta)
    (value : (AmbientPlane × AmbientPlane) → ℝ) :
    ∃ sample : List (NoisyUpperReading (AmbientPlane × AmbientPlane)),
      NoisyUpperSampleValid value sample ∧
        DeltaCoverage
          (ActiveOutputShortChordCore amplitude separation) sample delta ∧
        SampleInside
          (ActiveOutputShortChordCore amplitude separation) sample :=
  backwardCore_exists_finite_exactSample ha hseparation hdelta value

#print axioms audit_forward_core_closed
#print axioms audit_backward_core_closed
#print axioms audit_forward_core_compact
#print axioms audit_backward_core_compact
#print axioms audit_finite_delta_net
#print axioms audit_finite_exact_sample
#print axioms audit_finite_global_certificate
#print axioms audit_forward_core_sample
#print axioms audit_backward_core_sample

end BoundaryOfSelf.IntrinsicNonradialShearClosedCore
