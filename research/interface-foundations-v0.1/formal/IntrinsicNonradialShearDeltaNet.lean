import IntrinsicNonradialShearFiniteWitness

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearDeltaNet

open StandardHausdorffMetricBridge
open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearSpectralMap
open IntrinsicNonradialShearConditionChamber

structure NoisyUpperReading (α : Type*) where
  point : α
  measured : ℝ
  error : ℝ

noncomputable def noisySampleUpper {α : Type*} :
    List (NoisyUpperReading α) → ℝ
  | [] => 0
  | reading :: rest =>
      max (reading.measured + reading.error) (noisySampleUpper rest)

def NoisyUpperSampleValid {α : Type*}
    (value : α → ℝ) (sample : List (NoisyUpperReading α)) : Prop :=
  ∀ reading, reading ∈ sample →
    0 ≤ reading.error ∧
      |reading.measured - value reading.point| ≤ reading.error

def DeltaCoverage {α : Type*} [PseudoMetricSpace α]
    (domain : Set α) (sample : List (NoisyUpperReading α)) (delta : ℝ) : Prop :=
  ∀ point, point ∈ domain →
    ∃ reading, reading ∈ sample ∧ dist point reading.point ≤ delta

def RegularityCertificate {α : Type*} [PseudoMetricSpace α]
    (domain : Set α) (sample : List (NoisyUpperReading α))
    (constant : ℝ) (value : α → ℝ) : Prop :=
  ∀ point, point ∈ domain → ∀ reading, reading ∈ sample →
    |value point - value reading.point| ≤
      constant * dist point reading.point

lemma noisySampleUpper_nonneg
    {α : Type*} (sample : List (NoisyUpperReading α)) :
    0 ≤ noisySampleUpper sample := by
  induction sample with
  | nil => simp [noisySampleUpper]
  | cons reading rest ih =>
      rw [noisySampleUpper]
      exact le_max_of_le_right ih

lemma readingUpper_le_noisySampleUpper
    {α : Type*} {reading : NoisyUpperReading α}
    {sample : List (NoisyUpperReading α)}
    (hmem : reading ∈ sample) :
    reading.measured + reading.error ≤ noisySampleUpper sample := by
  induction sample with
  | nil => simp at hmem
  | cons head rest ih =>
      rw [noisySampleUpper]
      rcases List.mem_cons.mp hmem with heq | htail
      · subst reading
        exact le_max_left _ _
      · exact le_trans (ih htail) (le_max_right _ _)

lemma readingTrue_le_noisySampleUpper
    {α : Type*} {value : α → ℝ}
    {sample : List (NoisyUpperReading α)}
    (hvalid : NoisyUpperSampleValid value sample)
    {reading : NoisyUpperReading α} (hmem : reading ∈ sample) :
    value reading.point ≤ noisySampleUpper sample := by
  have hreading := hvalid reading hmem
  have htrue : value reading.point ≤ reading.measured + reading.error := by
    have habs := (abs_le.mp hreading.2).1
    linarith
  exact le_trans htrue (readingUpper_le_noisySampleUpper hmem)

theorem global_le_noisySampleUpper_add_regularity
    {α : Type*} [PseudoMetricSpace α]
    {domain : Set α} {sample : List (NoisyUpperReading α)}
    {delta constant : ℝ} {value : α → ℝ}
    (hconstant : 0 ≤ constant)
    (hvalid : NoisyUpperSampleValid value sample)
    (hcoverage : DeltaCoverage domain sample delta)
    (hregular :
      RegularityCertificate domain sample constant value) :
    ∀ point, point ∈ domain →
      value point ≤ noisySampleUpper sample + constant * delta := by
  intro point hpoint
  obtain ⟨reading, hmem, hdist⟩ := hcoverage point hpoint
  have hsample :=
    readingTrue_le_noisySampleUpper hvalid hmem
  have hreg := hregular point hpoint reading hmem
  have hdiff : value point - value reading.point ≤
      constant * dist point reading.point := by
    exact le_trans (le_abs_self _) hreg
  have hdelta :
      constant * dist point reading.point ≤ constant * delta :=
    mul_le_mul_of_nonneg_left hdist hconstant
  linarith

abbrev DistinctChord :=
  { pair : AmbientPlane × AmbientPlane // pair.1 ≠ pair.2 }

noncomputable def forwardChordRatio
    (amplitude : ℝ) (chord : DistinctChord) : ℝ :=
  dist (intrinsicShearMap amplitude chord.1.1)
      (intrinsicShearMap amplitude chord.1.2) /
    dist chord.1.1 chord.1.2

theorem forwardMapMetricBound_of_ratio_upper
    {amplitude upper : ℝ}
    (hupper : ∀ chord : DistinctChord,
      forwardChordRatio amplitude chord ≤ upper) :
    ForwardMapMetricBound amplitude upper := by
  intro first second
  by_cases heq : first = second
  · subst second
    simp
  · let chord : DistinctChord := ⟨(first, second), heq⟩
    have hdist : 0 < dist first second := dist_pos.2 heq
    have hratio := hupper chord
    dsimp [forwardChordRatio, chord] at hratio
    exact (div_le_iff₀ hdist).1 hratio

theorem forwardMapMetricBound_of_noisyDeltaCoverage
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
      (noisySampleUpper sample + regularity * delta) := by
  apply forwardMapMetricBound_of_ratio_upper
  intro chord
  exact global_le_noisySampleUpper_add_regularity
    hregularity hvalid hcoverage hregular chord (Set.mem_univ chord)

theorem forwardExactConstant_le_noisyDeltaCertificate
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
      noisySampleUpper sample + regularity * delta := by
  have hbound :=
    forwardMapMetricBound_of_noisyDeltaCoverage
      hregularity hvalid hcoverage hregular
  have hupper0 :
      0 ≤ noisySampleUpper sample + regularity * delta := by
    have hsample0 := noisySampleUpper_nonneg sample
    positivity
  exact (forward_map_metric_bound_iff ha hupper0).1 hbound

theorem amplitude_le_forward_noisyDeltaCertificate
    {amplitude delta regularity : ℝ} (ha : 0 ≤ amplitude)
    (hdelta : 0 ≤ delta) (hregularity : 0 ≤ regularity)
    {sample : List (NoisyUpperReading DistinctChord)}
    (hvalid :
      NoisyUpperSampleValid (forwardChordRatio amplitude) sample)
    (hcoverage : DeltaCoverage Set.univ sample delta)
    (hregular :
      RegularityCertificate Set.univ sample regularity
        (forwardChordRatio amplitude)) :
    amplitude ≤ noisySampleUpper sample + regularity * delta - 1 := by
  have hbase := one_add_le_forwardSpectralConstant ha
  have hupper :=
    forwardExactConstant_le_noisyDeltaCertificate
      ha hdelta hregularity hvalid hcoverage hregular
  linarith

lemma intrinsicShearMap_injective_on_chamber
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    Function.Injective (intrinsicShearMap amplitude) := by
  intro first second heq
  have hco :=
    intrinsicShearMap_colipschitz_inverseSpectralConstant
      ha ha1 first second
  rw [heq, dist_self, mul_zero] at hco
  exact dist_le_zero.mp hco

abbrev BackwardDistinctChord (amplitude : ℝ) :=
  { pair : AmbientPlane × AmbientPlane //
    intrinsicShearMap amplitude pair.1 ≠ intrinsicShearMap amplitude pair.2 }

noncomputable def backwardChordRatio
    (amplitude : ℝ) (chord : BackwardDistinctChord amplitude) : ℝ :=
  dist chord.1.1 chord.1.2 /
    dist (intrinsicShearMap amplitude chord.1.1)
      (intrinsicShearMap amplitude chord.1.2)

theorem backwardMapMetricBound_of_ratio_upper
    {amplitude upper : ℝ} (ha : 0 ≤ amplitude) (ha1 : amplitude < 1)
    (hupper : ∀ chord : BackwardDistinctChord amplitude,
      backwardChordRatio amplitude chord ≤ upper) :
    BackwardMapMetricBound amplitude upper := by
  intro first second
  by_cases heq : first = second
  · subst second
    simp
  · have hinjective := intrinsicShearMap_injective_on_chamber ha ha1
    have himage :
        intrinsicShearMap amplitude first ≠ intrinsicShearMap amplitude second := by
      intro h
      exact heq (hinjective h)
    let chord : BackwardDistinctChord amplitude :=
      ⟨(first, second), himage⟩
    have hdist :
        0 < dist (intrinsicShearMap amplitude first)
          (intrinsicShearMap amplitude second) :=
      dist_pos.2 himage
    have hratio := hupper chord
    dsimp [backwardChordRatio, chord] at hratio
    exact (div_le_iff₀ hdist).1 hratio

theorem backwardMapMetricBound_of_noisyDeltaCoverage
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
      (noisySampleUpper sample + regularity * delta) := by
  apply backwardMapMetricBound_of_ratio_upper ha ha1
  intro chord
  exact global_le_noisySampleUpper_add_regularity
    hregularity hvalid hcoverage hregular chord (Set.mem_univ chord)

theorem backwardExactConstant_le_noisyDeltaCertificate
    {amplitude delta regularity : ℝ}
    (ha : 0 ≤ amplitude) (ha1 : amplitude < 1)
    (hdelta : 0 ≤ delta) (hregularity : 0 ≤ regularity)
    {sample : List (NoisyUpperReading (BackwardDistinctChord amplitude))}
    (hvalid :
      NoisyUpperSampleValid (backwardChordRatio amplitude) sample)
    (hcoverage : DeltaCoverage Set.univ sample delta)
    (hregular :
      RegularityCertificate Set.univ sample regularity
        (backwardChordRatio amplitude)) :
    inverseSpectralConstant amplitude ≤
      noisySampleUpper sample + regularity * delta := by
  have hbound :=
    backwardMapMetricBound_of_noisyDeltaCoverage
      ha ha1 hregularity hvalid hcoverage hregular
  have hupper0 :
      0 ≤ noisySampleUpper sample + regularity * delta := by
    have hsample0 := noisySampleUpper_nonneg sample
    positivity
  exact (backward_map_metric_bound_iff ha ha1 hupper0).1 hbound

theorem amplitude_le_backward_noisyDeltaCertificate
    {amplitude delta regularity : ℝ}
    (ha : 0 ≤ amplitude) (ha1 : amplitude < 1)
    (hdelta : 0 ≤ delta) (hregularity : 0 ≤ regularity)
    {sample : List (NoisyUpperReading (BackwardDistinctChord amplitude))}
    (hvalid :
      NoisyUpperSampleValid (backwardChordRatio amplitude) sample)
    (hcoverage : DeltaCoverage Set.univ sample delta)
    (hregular :
      RegularityCertificate Set.univ sample regularity
        (backwardChordRatio amplitude)) :
    amplitude ≤
      ((noisySampleUpper sample + regularity * delta) - 1) /
        (noisySampleUpper sample + regularity * delta) := by
  let upper : ℝ := noisySampleUpper sample + regularity * delta
  have hconstant :=
    backwardExactConstant_le_noisyDeltaCertificate
      ha ha1 hdelta hregularity hvalid hcoverage hregular
  have hbase := inverse_axial_le_inverseSpectralConstant ha ha1
  have hupperOne : 1 ≤ upper := by
    have hden : 0 < 1 - amplitude := by linarith
    have hone : 1 ≤ 1 / (1 - amplitude) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    exact le_trans hone (le_trans hbase hconstant)
  have hupperPos : 0 < upper := lt_of_lt_of_le zero_lt_one hupperOne
  have hscaled : 1 ≤ upper * (1 - amplitude) := by
    have hden : 0 < 1 - amplitude := by linarith
    have h := le_trans hbase hconstant
    exact (div_le_iff₀ hden).1 h
  dsimp [upper] at *
  apply (le_div_iff₀ hupperPos).2
  nlinarith

theorem amplitude_le_twoSided_noisyDeltaCertificate
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
            backwardRegularity * backwardDelta)) := by
  let forwardUpper : ℝ :=
    noisySampleUpper forwardSample + forwardRegularity * forwardDelta
  let backwardUpper : ℝ :=
    noisySampleUpper backwardSample + backwardRegularity * backwardDelta
  have hforward :=
    forwardMapMetricBound_of_noisyDeltaCoverage
      hforwardRegularity hforwardValid hforwardCoverage hforwardCertificate
  have hbackward :=
    backwardMapMetricBound_of_noisyDeltaCoverage
      ha ha1 hbackwardRegularity hbackwardValid
        hbackwardCoverage hbackwardCertificate
  have hforward0 : 0 ≤ forwardUpper := by
    dsimp [forwardUpper]
    have hsample := noisySampleUpper_nonneg forwardSample
    positivity
  have hbackward0 : 0 ≤ backwardUpper := by
    dsimp [backwardUpper]
    have hsample := noisySampleUpper_nonneg backwardSample
    positivity
  have hbound :=
    observed_distortion_bounds_amplitude
      ha ha1 hforward0 hbackward0 ⟨hforward, hbackward⟩
  exact hbound

end BoundaryOfSelf.IntrinsicNonradialShearDeltaNet
