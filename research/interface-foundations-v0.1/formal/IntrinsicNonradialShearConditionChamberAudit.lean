import IntrinsicNonradialShearConditionChamber

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearConditionChamber

open IntrinsicNonradialShearSpectralMap

theorem audit_forward_strict
    {first second : ℝ} (hfirst : 0 ≤ first) (horder : first < second) :
    forwardSpectralConstant first < forwardSpectralConstant second :=
  forwardSpectralConstant_strictMono hfirst horder

theorem audit_inverse_strict
    {first second : ℝ}
    (hfirst : 0 ≤ first) (horder : first < second) (hsecondOne : second < 1) :
    inverseSpectralConstant first < inverseSpectralConstant second :=
  inverseSpectralConstant_strictMono hfirst horder hsecondOne

theorem audit_condition_origin :
    conditionNumber 0 = 1 :=
  conditionNumber_zero

theorem audit_condition_lower
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    1 ≤ conditionNumber amplitude :=
  one_le_conditionNumber ha ha1

theorem audit_condition_strict
    {first second : ℝ}
    (hfirst : 0 ≤ first) (horder : first < second) (hsecondOne : second < 1) :
    conditionNumber first < conditionNumber second :=
  conditionNumber_strictMono hfirst horder hsecondOne

theorem audit_condition_identifies_amplitude
    {first second : ℝ}
    (hfirst : 0 ≤ first) (hfirstOne : first < 1)
    (hsecond : 0 ≤ second) (hsecondOne : second < 1)
    (hequal : conditionNumber first = conditionNumber second) :
    first = second :=
  conditionNumber_injective_on_chamber
    hfirst hfirstOne hsecond hsecondOne hequal

theorem audit_observation_exact
    {amplitude forwardObserved backwardObserved : ℝ}
    (ha : 0 ≤ amplitude) (ha1 : amplitude < 1)
    (hf : 0 ≤ forwardObserved) (hb : 0 ≤ backwardObserved) :
    DistortionObservation amplitude forwardObserved backwardObserved ↔
      forwardSpectralConstant amplitude ≤ forwardObserved ∧
        inverseSpectralConstant amplitude ≤ backwardObserved :=
  distortionObservation_iff_exactConstants ha ha1 hf hb

theorem audit_feasible_set_downward
    {forwardObserved backwardObserved first second : ℝ}
    (hfirst : FeasibleAmplitude forwardObserved backwardObserved first)
    (hsecond0 : 0 ≤ second) (horder : second ≤ first) :
    FeasibleAmplitude forwardObserved backwardObserved second :=
  feasibleAmplitude_downward hfirst hsecond0 horder

theorem audit_explicit_amplitude_bound
    {amplitude forwardObserved backwardObserved : ℝ}
    (ha : 0 ≤ amplitude) (ha1 : amplitude < 1)
    (hf : 0 ≤ forwardObserved) (hb : 0 ≤ backwardObserved)
    (hobs : DistortionObservation amplitude forwardObserved backwardObserved) :
    amplitude ≤
      min (forwardObserved - 1)
        ((backwardObserved - 1) / backwardObserved) :=
  observed_distortion_bounds_amplitude ha ha1 hf hb hobs

#print axioms audit_forward_strict
#print axioms audit_inverse_strict
#print axioms audit_condition_origin
#print axioms audit_condition_lower
#print axioms audit_condition_strict
#print axioms audit_condition_identifies_amplitude
#print axioms audit_observation_exact
#print axioms audit_feasible_set_downward
#print axioms audit_explicit_amplitude_bound

end BoundaryOfSelf.IntrinsicNonradialShearConditionChamber
