import IntrinsicNonradialShearDeltaNet

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearDeltaNet

open IntrinsicNonradialShearSpectralMap
open IntrinsicNonradialShearConditionChamber

theorem audit_abstract_delta_upper
    {α : Type*} [PseudoMetricSpace α]
    {domain : Set α} {sample : List (NoisyUpperReading α)}
    {delta constant : ℝ} {value : α → ℝ}
    (hconstant : 0 ≤ constant)
    (hvalid : NoisyUpperSampleValid value sample)
    (hcoverage : DeltaCoverage domain sample delta)
    (hregular :
      RegularityCertificate domain sample constant value) :
    ∀ point, point ∈ domain →
      value point ≤ noisySampleUpper sample + constant * delta :=
  global_le_noisySampleUpper_add_regularity
    hconstant hvalid hcoverage hregular

theorem audit_forward_global_certificate
    {amplitude delta regularity : ℝ}
    {sample : List (NoisyUpperReading DistinctChord)}
    (hregularity : 0 ≤ regularity)
    (hvalid :
      NoisyUpperSampleValid (forwardChordRatio amplitude) sample)
    (hcoverage : DeltaCoverage Set.univ sample delta)
    (hregular :
      RegularityCertificate Set.univ sample regularity
        (forwardChordRatio amplitude)) :
    ForwardMapMetricBound amplitude
      (noisySampleUpper sample + regularity * delta) :=
  forwardMapMetricBound_of_noisyDeltaCoverage
    hregularity hvalid hcoverage hregular

theorem audit_forward_exact_upper
    {amplitude delta regularity : ℝ} (ha : 0 ≤ amplitude)
    (hdelta : 0 ≤ delta) (hregularity : 0 ≤ regularity)
    {sample : List (NoisyUpperReading DistinctChord)}
    (hvalid :
      NoisyUpperSampleValid (forwardChordRatio amplitude) sample)
    (hcoverage : DeltaCoverage Set.univ sample delta)
    (hregular :
      RegularityCertificate Set.univ sample regularity
        (forwardChordRatio amplitude)) :
    forwardSpectralConstant amplitude ≤
      noisySampleUpper sample + regularity * delta :=
  forwardExactConstant_le_noisyDeltaCertificate
    ha hdelta hregularity hvalid hcoverage hregular

theorem audit_backward_global_certificate
    {amplitude delta regularity : ℝ}
    (ha : 0 ≤ amplitude) (ha1 : amplitude < 1)
    {sample : List (NoisyUpperReading (BackwardDistinctChord amplitude))}
    (hregularity : 0 ≤ regularity)
    (hvalid :
      NoisyUpperSampleValid (backwardChordRatio amplitude) sample)
    (hcoverage : DeltaCoverage Set.univ sample delta)
    (hregular :
      RegularityCertificate Set.univ sample regularity
        (backwardChordRatio amplitude)) :
    BackwardMapMetricBound amplitude
      (noisySampleUpper sample + regularity * delta) :=
  backwardMapMetricBound_of_noisyDeltaCoverage
    ha ha1 hregularity hvalid hcoverage hregular

theorem audit_two_sided_amplitude_certificate
    {amplitude forwardDelta forwardRegularity
      backwardDelta backwardRegularity : ℝ}
    (ha : 0 ≤ amplitude) (ha1 : amplitude < 1)
    (hforwardDelta : 0 ≤ forwardDelta)
    (hforwardRegularity : 0 ≤ forwardRegularity)
    (hbackwardDelta : 0 ≤ backwardDelta)
    (hbackwardRegularity : 0 ≤ backwardRegularity)
    {forwardSample : List (NoisyUpperReading DistinctChord)}
    {backwardSample :
      List (NoisyUpperReading (BackwardDistinctChord amplitude))}
    (hforwardValid :
      NoisyUpperSampleValid (forwardChordRatio amplitude) forwardSample)
    (hforwardCoverage :
      DeltaCoverage Set.univ forwardSample forwardDelta)
    (hforwardCertificate :
      RegularityCertificate Set.univ forwardSample forwardRegularity
        (forwardChordRatio amplitude))
    (hbackwardValid :
      NoisyUpperSampleValid (backwardChordRatio amplitude) backwardSample)
    (hbackwardCoverage :
      DeltaCoverage Set.univ backwardSample backwardDelta)
    (hbackwardCertificate :
      RegularityCertificate Set.univ backwardSample backwardRegularity
        (backwardChordRatio amplitude)) :
    amplitude ≤
      min
        (noisySampleUpper forwardSample +
          forwardRegularity * forwardDelta - 1)
        (((noisySampleUpper backwardSample +
            backwardRegularity * backwardDelta) - 1) /
          (noisySampleUpper backwardSample +
            backwardRegularity * backwardDelta)) :=
  amplitude_le_twoSided_noisyDeltaCertificate
    ha ha1 hforwardDelta hforwardRegularity
    hbackwardDelta hbackwardRegularity
    hforwardValid hforwardCoverage hforwardCertificate
    hbackwardValid hbackwardCoverage hbackwardCertificate

#print axioms audit_abstract_delta_upper
#print axioms audit_forward_global_certificate
#print axioms audit_forward_exact_upper
#print axioms audit_backward_global_certificate
#print axioms audit_two_sided_amplitude_certificate

end BoundaryOfSelf.IntrinsicNonradialShearDeltaNet
