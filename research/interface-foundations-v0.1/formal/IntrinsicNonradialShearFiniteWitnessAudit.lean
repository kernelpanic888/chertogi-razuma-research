import IntrinsicNonradialShearFiniteWitness

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearFiniteWitness

open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearSpectralMap
open IntrinsicNonradialShearConditionChamber

theorem audit_forward_finite_sound
    {amplitude : ℝ} (ha : 0 ≤ amplitude)
    {sample : List ChordReading}
    (hvalid : ForwardSampleValid amplitude sample) :
    sampleLower sample ≤ forwardSpectralConstant amplitude :=
  forwardSample_lower_le_exactConstant ha hvalid

theorem audit_backward_finite_sound
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (ha1 : amplitude < 1)
    {sample : List ChordReading}
    (hvalid : BackwardSampleValid amplitude sample) :
    sampleLower sample ≤ inverseSpectralConstant amplitude :=
  backwardSample_lower_le_exactConstant ha ha1 hvalid

theorem audit_forward_noise_sound
    {trueInput trueOutput measuredInput measuredOutput inputError outputError : ℝ}
    (htrueInput : 0 ≤ trueInput) (htrueOutput : 0 ≤ trueOutput)
    (hinputError : 0 ≤ inputError) (houtputError : 0 ≤ outputError)
    (hinput : |measuredInput - trueInput| ≤ inputError)
    (houtput : |measuredOutput - trueOutput| ≤ outputError)
    (hden : 0 < measuredInput + inputError)
    (hnumerator : outputError ≤ measuredOutput) :
    0 ≤ forwardNoiseLower
        measuredInput measuredOutput inputError outputError ∧
      forwardNoiseLower measuredInput measuredOutput inputError outputError *
          trueInput ≤ trueOutput :=
  forwardNoiseLower_sound
    htrueInput htrueOutput hinputError houtputError
    hinput houtput hden hnumerator

theorem audit_backward_noise_sound
    {trueInput trueOutput measuredInput measuredOutput inputError outputError : ℝ}
    (htrueInput : 0 ≤ trueInput) (htrueOutput : 0 ≤ trueOutput)
    (hinputError : 0 ≤ inputError) (houtputError : 0 ≤ outputError)
    (hinput : |measuredInput - trueInput| ≤ inputError)
    (houtput : |measuredOutput - trueOutput| ≤ outputError)
    (hden : 0 < measuredOutput + outputError)
    (hnumerator : inputError ≤ measuredInput) :
    0 ≤ backwardNoiseLower
        measuredInput measuredOutput inputError outputError ∧
      backwardNoiseLower measuredInput measuredOutput inputError outputError *
          trueOutput ≤ trueInput :=
  backwardNoiseLower_sound
    htrueInput htrueOutput hinputError houtputError
    hinput houtput hden hnumerator

theorem audit_forward_exclusion
    {actual candidate : ℝ}
    (hactual : 0 ≤ actual) (hcandidate : 0 ≤ candidate)
    {sample : List ChordReading}
    (hvalid : ForwardSampleValid actual sample)
    (hthreshold :
      forwardSpectralConstant candidate < sampleLower sample) :
    candidate < actual :=
  forwardSample_excludes_smallerCandidate
    hactual hcandidate hvalid hthreshold

theorem audit_backward_exclusion
    {actual candidate : ℝ}
    (hactual : 0 ≤ actual) (hactual1 : actual < 1)
    (hcandidate : 0 ≤ candidate) (hcandidate1 : candidate < 1)
    {sample : List ChordReading}
    (hvalid : BackwardSampleValid actual sample)
    (hthreshold :
      inverseSpectralConstant candidate < sampleLower sample) :
    candidate < actual :=
  backwardSample_excludes_smallerCandidate
    hactual hactual1 hcandidate hcandidate1 hvalid hthreshold

theorem audit_two_sided_interval
    {actual candidate forwardObserved backwardObserved : ℝ}
    (hactual : 0 ≤ actual) (hactual1 : actual < 1)
    (hcandidate : 0 ≤ candidate)
    (hforwardObserved : 0 ≤ forwardObserved)
    (hbackwardObserved : 0 ≤ backwardObserved)
    (hglobal :
      DistortionObservation actual forwardObserved backwardObserved)
    {sample : List ChordReading}
    (hvalid : ForwardSampleValid actual sample)
    (hthreshold :
      forwardSpectralConstant candidate < sampleLower sample) :
    candidate < actual ∧
      actual ≤
        min (forwardObserved - 1)
          ((backwardObserved - 1) / backwardObserved) :=
  forwardSample_and_globalBounds_interval
    hactual hactual1 hcandidate hforwardObserved hbackwardObserved
    hglobal hvalid hthreshold

#print axioms audit_forward_finite_sound
#print axioms audit_backward_finite_sound
#print axioms audit_forward_noise_sound
#print axioms audit_backward_noise_sound
#print axioms audit_forward_exclusion
#print axioms audit_backward_exclusion
#print axioms audit_two_sided_interval

end BoundaryOfSelf.IntrinsicNonradialShearFiniteWitness
