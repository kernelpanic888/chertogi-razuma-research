import IntrinsicNonradialShearConditionChamber

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearFiniteWitness

open StandardHausdorffMetricBridge
open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearSpectralMap
open IntrinsicNonradialShearConditionChamber

structure ChordReading where
  first : AmbientPlane
  second : AmbientPlane
  lower : ℝ

def sampleLower : List ChordReading → ℝ
  | [] => 0
  | reading :: rest => max reading.lower (sampleLower rest)

def ForwardChordValid (amplitude : ℝ) (reading : ChordReading) : Prop :=
  reading.first ≠ reading.second ∧
    0 ≤ reading.lower ∧
      reading.lower * dist reading.first reading.second ≤
        dist (intrinsicShearMap amplitude reading.first)
          (intrinsicShearMap amplitude reading.second)

def BackwardChordValid (amplitude : ℝ) (reading : ChordReading) : Prop :=
  intrinsicShearMap amplitude reading.first ≠
      intrinsicShearMap amplitude reading.second ∧
    0 ≤ reading.lower ∧
      reading.lower *
          dist (intrinsicShearMap amplitude reading.first)
            (intrinsicShearMap amplitude reading.second) ≤
        dist reading.first reading.second

def ForwardSampleValid
    (amplitude : ℝ) (sample : List ChordReading) : Prop :=
  ∀ reading, reading ∈ sample → ForwardChordValid amplitude reading

def BackwardSampleValid
    (amplitude : ℝ) (sample : List ChordReading) : Prop :=
  ∀ reading, reading ∈ sample → BackwardChordValid amplitude reading

lemma sampleLower_le
    {sample : List ChordReading} {constant : ℝ}
    (hzero : 0 ≤ constant)
    (hreadings : ∀ reading, reading ∈ sample → reading.lower ≤ constant) :
    sampleLower sample ≤ constant := by
  induction sample with
  | nil =>
      simpa [sampleLower] using hzero
  | cons reading rest ih =>
      rw [sampleLower]
      apply max_le
      · exact hreadings reading (by simp)
      · apply ih
        intro item hitem
        exact hreadings item (by simp [hitem])

lemma forwardChord_lower_le_exactConstant
    {amplitude : ℝ} (ha : 0 ≤ amplitude)
    {reading : ChordReading}
    (hvalid : ForwardChordValid amplitude reading) :
    reading.lower ≤ forwardSpectralConstant amplitude := by
  rcases hvalid with ⟨hne, _hlower, hwitness⟩
  have hdist : 0 < dist reading.first reading.second :=
    dist_pos.2 hne
  have hglobal :=
    intrinsicShearMap_dist_le_forwardSpectralConstant
      ha reading.first reading.second
  nlinarith

theorem forwardSample_lower_le_exactConstant
    {amplitude : ℝ} (ha : 0 ≤ amplitude)
    {sample : List ChordReading}
    (hvalid : ForwardSampleValid amplitude sample) :
    sampleLower sample ≤ forwardSpectralConstant amplitude := by
  apply sampleLower_le (Real.sqrt_nonneg _)
  intro reading hmem
  exact forwardChord_lower_le_exactConstant ha (hvalid reading hmem)

lemma backwardChord_lower_le_exactConstant
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (ha1 : amplitude < 1)
    {reading : ChordReading}
    (hvalid : BackwardChordValid amplitude reading) :
    reading.lower ≤ inverseSpectralConstant amplitude := by
  rcases hvalid with ⟨hne, _hlower, hwitness⟩
  have hdist :
      0 < dist
        (intrinsicShearMap amplitude reading.first)
        (intrinsicShearMap amplitude reading.second) :=
    dist_pos.2 hne
  have hglobal :=
    intrinsicShearMap_colipschitz_inverseSpectralConstant
      ha ha1 reading.first reading.second
  nlinarith

theorem backwardSample_lower_le_exactConstant
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (ha1 : amplitude < 1)
    {sample : List ChordReading}
    (hvalid : BackwardSampleValid amplitude sample) :
    sampleLower sample ≤ inverseSpectralConstant amplitude := by
  apply sampleLower_le (Real.sqrt_nonneg _)
  intro reading hmem
  exact backwardChord_lower_le_exactConstant
    ha ha1 (hvalid reading hmem)

noncomputable def forwardNoiseLower
    (measuredInput measuredOutput inputError outputError : ℝ) : ℝ :=
  (measuredOutput - outputError) / (measuredInput + inputError)

noncomputable def backwardNoiseLower
    (measuredInput measuredOutput inputError outputError : ℝ) : ℝ :=
  (measuredInput - inputError) / (measuredOutput + outputError)

theorem forwardNoiseLower_sound
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
          trueInput ≤ trueOutput := by
  have htrueInputUpper : trueInput ≤ measuredInput + inputError := by
    have habs := (abs_le.mp hinput).1
    linarith
  have htrueOutputLower : measuredOutput - outputError ≤ trueOutput := by
    have habs := (abs_le.mp houtput).2
    linarith
  have hlower0 :
      0 ≤ forwardNoiseLower
        measuredInput measuredOutput inputError outputError := by
    dsimp [forwardNoiseLower]
    positivity
  refine ⟨hlower0, ?_⟩
  have hmul :=
    mul_le_mul_of_nonneg_left htrueInputUpper hlower0
  have hcancel :
      forwardNoiseLower measuredInput measuredOutput inputError outputError *
          (measuredInput + inputError) =
        measuredOutput - outputError := by
    dsimp [forwardNoiseLower]
    field_simp
  rw [hcancel] at hmul
  exact le_trans hmul htrueOutputLower

theorem backwardNoiseLower_sound
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
          trueOutput ≤ trueInput := by
  have htrueOutputUpper : trueOutput ≤ measuredOutput + outputError := by
    have habs := (abs_le.mp houtput).1
    linarith
  have htrueInputLower : measuredInput - inputError ≤ trueInput := by
    have habs := (abs_le.mp hinput).2
    linarith
  have hlower0 :
      0 ≤ backwardNoiseLower
        measuredInput measuredOutput inputError outputError := by
    dsimp [backwardNoiseLower]
    positivity
  refine ⟨hlower0, ?_⟩
  have hmul :=
    mul_le_mul_of_nonneg_left htrueOutputUpper hlower0
  have hcancel :
      backwardNoiseLower measuredInput measuredOutput inputError outputError *
          (measuredOutput + outputError) =
        measuredInput - inputError := by
    dsimp [backwardNoiseLower]
    field_simp
  rw [hcancel] at hmul
  exact le_trans hmul htrueInputLower

theorem noisyForwardReading_valid
    {amplitude measuredInput measuredOutput inputError outputError : ℝ}
    {first second : AmbientPlane}
    (hne : first ≠ second)
    (hinputError : 0 ≤ inputError) (houtputError : 0 ≤ outputError)
    (hinput :
      |measuredInput - dist first second| ≤ inputError)
    (houtput :
      |measuredOutput -
        dist (intrinsicShearMap amplitude first)
          (intrinsicShearMap amplitude second)| ≤ outputError)
    (hden : 0 < measuredInput + inputError)
    (hnumerator : outputError ≤ measuredOutput) :
    ForwardChordValid amplitude
      { first := first
        second := second
        lower := forwardNoiseLower
          measuredInput measuredOutput inputError outputError } := by
  have hsound :=
    forwardNoiseLower_sound
      (dist_nonneg : 0 ≤ dist first second)
      (dist_nonneg :
        0 ≤ dist (intrinsicShearMap amplitude first)
          (intrinsicShearMap amplitude second))
      hinputError houtputError hinput houtput hden hnumerator
  exact ⟨hne, hsound.1, hsound.2⟩

theorem noisyBackwardReading_valid
    {amplitude measuredInput measuredOutput inputError outputError : ℝ}
    {first second : AmbientPlane}
    (hne :
      intrinsicShearMap amplitude first ≠
        intrinsicShearMap amplitude second)
    (hinputError : 0 ≤ inputError) (houtputError : 0 ≤ outputError)
    (hinput :
      |measuredInput - dist first second| ≤ inputError)
    (houtput :
      |measuredOutput -
        dist (intrinsicShearMap amplitude first)
          (intrinsicShearMap amplitude second)| ≤ outputError)
    (hden : 0 < measuredOutput + outputError)
    (hnumerator : inputError ≤ measuredInput) :
    BackwardChordValid amplitude
      { first := first
        second := second
        lower := backwardNoiseLower
          measuredInput measuredOutput inputError outputError } := by
  have hsound :=
    backwardNoiseLower_sound
      (dist_nonneg : 0 ≤ dist first second)
      (dist_nonneg :
        0 ≤ dist (intrinsicShearMap amplitude first)
          (intrinsicShearMap amplitude second))
      hinputError houtputError hinput houtput hden hnumerator
  exact ⟨hne, hsound.1, hsound.2⟩

theorem forwardSample_excludes_smallerCandidate
    {actual candidate : ℝ}
    (hactual : 0 ≤ actual) (hcandidate : 0 ≤ candidate)
    {sample : List ChordReading}
    (hvalid : ForwardSampleValid actual sample)
    (hthreshold :
      forwardSpectralConstant candidate < sampleLower sample) :
    candidate < actual := by
  have hsample :=
    forwardSample_lower_le_exactConstant hactual hvalid
  by_contra hnot
  have horder : actual ≤ candidate := le_of_not_gt hnot
  have hmono :=
    forwardSpectralConstant_mono hactual horder
  linarith

theorem backwardSample_excludes_smallerCandidate
    {actual candidate : ℝ}
    (hactual : 0 ≤ actual) (hactual1 : actual < 1)
    (hcandidate : 0 ≤ candidate) (hcandidate1 : candidate < 1)
    {sample : List ChordReading}
    (hvalid : BackwardSampleValid actual sample)
    (hthreshold :
      inverseSpectralConstant candidate < sampleLower sample) :
    candidate < actual := by
  have hsample :=
    backwardSample_lower_le_exactConstant hactual hactual1 hvalid
  by_contra hnot
  have horder : actual ≤ candidate := le_of_not_gt hnot
  have hmono :=
    inverseSpectralConstant_mono hactual horder hcandidate1
  linarith

theorem forwardSample_and_globalBounds_interval
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
          ((backwardObserved - 1) / backwardObserved) := by
  exact ⟨
    forwardSample_excludes_smallerCandidate
      hactual hcandidate hvalid hthreshold,
    observed_distortion_bounds_amplitude
      hactual hactual1 hforwardObserved hbackwardObserved hglobal⟩

theorem backwardSample_and_globalBounds_interval
    {actual candidate forwardObserved backwardObserved : ℝ}
    (hactual : 0 ≤ actual) (hactual1 : actual < 1)
    (hcandidate : 0 ≤ candidate) (hcandidate1 : candidate < 1)
    (hforwardObserved : 0 ≤ forwardObserved)
    (hbackwardObserved : 0 ≤ backwardObserved)
    (hglobal :
      DistortionObservation actual forwardObserved backwardObserved)
    {sample : List ChordReading}
    (hvalid : BackwardSampleValid actual sample)
    (hthreshold :
      inverseSpectralConstant candidate < sampleLower sample) :
    candidate < actual ∧
      actual ≤
        min (forwardObserved - 1)
          ((backwardObserved - 1) / backwardObserved) := by
  exact ⟨
    backwardSample_excludes_smallerCandidate
      hactual hactual1 hcandidate hcandidate1 hvalid hthreshold,
    observed_distortion_bounds_amplitude
      hactual hactual1 hforwardObserved hbackwardObserved hglobal⟩

end BoundaryOfSelf.IntrinsicNonradialShearFiniteWitness
