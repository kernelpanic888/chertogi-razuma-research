import IntrinsicNonradialShearNoisyIdentifiability

namespace BoundaryOfSelf.IntrinsicNonradialShearNoisyIdentifiabilityAudit

open Set
open IntrinsicNonradialShearNoisyIdentifiability

theorem audited_direct_outer_envelope
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    exactDirectMetricConstant amplitude ≤ 1 + Real.sqrt 2 * amplitude :=
  exactDirectMetricConstant_le_sqrtTwoEnvelope ha0

theorem audited_certified_interval
    {amplitude forwardObserved inverseObserved forwardError inverseError : ℝ}
    (hreading : CertifiedNoisyMetricReading amplitude
      forwardObserved inverseObserved forwardError inverseError) :
    amplitude ∈ Set.Icc
      (noisyAmplitudeLower forwardObserved forwardError)
      (noisyAmplitudeUpper forwardObserved inverseObserved
        forwardError inverseError) :=
  certified_reading_amplitude_mem_interval hreading

theorem audited_feasible_subset
    (forwardObserved inverseObserved forwardError inverseError : ℝ) :
    NoisyFeasibleAmplitudes forwardObserved inverseObserved
        forwardError inverseError ⊆
      Set.Icc (noisyAmplitudeLower forwardObserved forwardError)
        (noisyAmplitudeUpper forwardObserved inverseObserved
          forwardError inverseError) :=
  noisyFeasibleAmplitudes_subset_interval
    forwardObserved inverseObserved forwardError inverseError

theorem audited_nonempty_from_true_reading
    {amplitude forwardObserved inverseObserved forwardError inverseError : ℝ}
    (hreading : CertifiedNoisyMetricReading amplitude
      forwardObserved inverseObserved forwardError inverseError) :
    (NoisyFeasibleAmplitudes forwardObserved inverseObserved
      forwardError inverseError).Nonempty :=
  certified_reading_feasible_nonempty hreading

theorem audited_zero_error_unique
    {forwardObserved inverseObserved first second : ℝ}
    (hfirst : CertifiedNoisyMetricReading first
      forwardObserved inverseObserved 0 0)
    (hsecond : CertifiedNoisyMetricReading second
      forwardObserved inverseObserved 0 0) :
    first = second :=
  zero_error_reading_unique hfirst hsecond

#print axioms audited_direct_outer_envelope
#print axioms audited_certified_interval
#print axioms audited_feasible_subset
#print axioms audited_nonempty_from_true_reading
#print axioms audited_zero_error_unique

end BoundaryOfSelf.IntrinsicNonradialShearNoisyIdentifiabilityAudit
