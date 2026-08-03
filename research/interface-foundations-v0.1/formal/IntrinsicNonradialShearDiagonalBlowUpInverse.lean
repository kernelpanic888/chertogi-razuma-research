import IntrinsicNonradialShearDiagonalBlowUp

open scoped Topology RealInnerProductSpace
open Set Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearDiagonalBlowUpInverse

noncomputable section

open StandardHausdorffMetricBridge
open IntrinsicNonradialShearKernelSharp
open IntrinsicNonradialShearDiagonalBlowUp

/-! ## IF-BS-22F-F8C13: inverse blow-up and exact relaxed envelopes -/

/-- The inverse chamber is stable while the maximal relaxed vertical cancellation
stays strictly below one. -/
def AdmissibleAmplitude (amplitude : ℝ) : Prop :=
  0 ≤ amplitude ∧ Real.sqrt 2 * amplitude < 1

/-- Exact lower squared envelope of the relaxed blow-up chamber. -/
def relaxedLowerSq (amplitude : ℝ) : ℝ :=
  (1 - Real.sqrt 2 * amplitude) ^ 2

/-- Exact upper squared envelope of the relaxed blow-up chamber. -/
def relaxedUpperSq (amplitude : ℝ) : ℝ :=
  (1 + Real.sqrt 2 * amplitude) ^ 2

/-- Reciprocal observable governing the inverse stretch of a represented chord. -/
def inverseBlowUpSq (amplitude : ℝ) (point : BlowUpPoint) : ℝ :=
  (forwardBlowUpSq amplitude point)⁻¹

/-- Explicit modulus for the reciprocal observable on the admissible chamber. -/
def inverseBlowUpSqRegularity (amplitude : ℝ) : ℝ :=
  forwardBlowUpSqRegularity amplitude / (relaxedLowerSq amplitude) ^ 2

lemma sqrt_two_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2

lemma sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := by
  norm_num

lemma kernelOrigin_eq_zero : kernelOrigin = 0 := by
  ext index
  fin_cases index <;> simp [kernelOrigin, planeEmbedding]

lemma chamber_unit_and_slope
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalBlowUpChamber) :
    point.1.ofLp 0 ^ 2 + point.1.ofLp 1 ^ 2 = 1 ∧
      |point.2| ≤ Real.sqrt 2 := by
  rcases hpoint with ⟨hdirection, hslope⟩
  have hdist : dist point.1 kernelOrigin = 1 := Metric.mem_sphere.mp hdirection
  have hnorm : ‖point.1‖ = 1 := by
    simpa [dist_eq_norm, kernelOrigin_eq_zero] using hdist
  have hunit : point.1.ofLp 0 ^ 2 + point.1.ofLp 1 ^ 2 = 1 := by
    calc
      point.1.ofLp 0 ^ 2 + point.1.ofLp 1 ^ 2 = ‖point.1‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp [Fin.sum_univ_two, Real.norm_eq_abs]
      _ = 1 := by rw [hnorm]; norm_num
  have hslope' : -Real.sqrt 2 ≤ point.2 ∧ point.2 ≤ Real.sqrt 2 :=
    Set.mem_Icc.mp hslope
  have habs : |point.2| ≤ Real.sqrt 2 :=
    abs_le.mpr ⟨hslope'.1, hslope'.2⟩
  exact ⟨hunit, habs⟩

lemma chamber_vertical_abs_le_one
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalBlowUpChamber) :
    |point.1.ofLp 1| ≤ 1 := by
  have hunit := (chamber_unit_and_slope hpoint).1
  have hy_sq : point.1.ofLp 1 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (point.1.ofLp 0)]
  have habs_sq : |point.1.ofLp 1| ^ 2 ≤ (1 : ℝ) ^ 2 := by
    simpa [sq_abs] using hy_sq
  exact (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp habs_sq

lemma perturbation_abs_le
    {amplitude : ℝ}
    (ha : 0 ≤ amplitude)
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalBlowUpChamber) :
    |amplitude * point.2| ≤ Real.sqrt 2 * amplitude := by
  rw [abs_mul, abs_of_nonneg ha]
  nlinarith [chamber_unit_and_slope hpoint |>.2]

lemma forwardBlowUpSq_expansion
    (amplitude : ℝ)
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalBlowUpChamber) :
    forwardBlowUpSq amplitude point =
      1 + 2 * point.1.ofLp 1 * (amplitude * point.2) +
        (amplitude * point.2) ^ 2 := by
  have hunit := (chamber_unit_and_slope hpoint).1
  simp only [forwardBlowUpSq]
  nlinarith

lemma mixed_term_abs_le_perturbation
    {amplitude : ℝ}
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalBlowUpChamber) :
    |point.1.ofLp 1 * (amplitude * point.2)| ≤ |amplitude * point.2| := by
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (chamber_vertical_abs_le_one hpoint)

theorem relaxed_envelope
    {amplitude : ℝ}
    (hadm : AdmissibleAmplitude amplitude)
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalBlowUpChamber) :
    relaxedLowerSq amplitude ≤ forwardBlowUpSq amplitude point ∧
      forwardBlowUpSq amplitude point ≤ relaxedUpperSq amplitude := by
  rcases hadm with ⟨ha, hsmall⟩
  let b : ℝ := amplitude * point.2
  let t : ℝ := Real.sqrt 2 * amplitude
  let c : ℝ := |b|
  have hc0 : 0 ≤ c := abs_nonneg _
  have ht0 : 0 ≤ t := mul_nonneg sqrt_two_nonneg ha
  have hct : c ≤ t := by
    dsimp [c, b, t]
    exact perturbation_abs_le ha hpoint
  have ht1 : t ≤ 1 := le_of_lt hsmall
  have hmixed := mixed_term_abs_le_perturbation (amplitude := amplitude) hpoint
  have hmixed_bounds : -c ≤ point.1.ofLp 1 * b ∧ point.1.ofLp 1 * b ≤ c := by
    dsimp [c, b] at hmixed ⊢
    exact abs_le.mp hmixed
  have hb_sq : b ^ 2 = c ^ 2 := by
    dsimp [c]
    simpa [sq_abs]
  have hdecreasing : -2 * t + t ^ 2 ≤ -2 * c + c ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hct) (by nlinarith : 0 ≤ 2 - t - c)]
  have hupper : 2 * c + c ^ 2 ≤ 2 * t + t ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hct) (by positivity : 0 ≤ 2 + t + c)]
  have hexpand := forwardBlowUpSq_expansion amplitude hpoint
  constructor <;> dsimp [relaxedLowerSq, relaxedUpperSq] <;>
    dsimp [t] at * <;> nlinarith

/-- North-pole direction with maximally cancelling slope. -/
def relaxedLowerWitness : BlowUpPoint :=
  (planeEmbedding ⟨0, 1⟩, -Real.sqrt 2)

/-- North-pole direction with maximally reinforcing slope. -/
def relaxedUpperWitness : BlowUpPoint :=
  (planeEmbedding ⟨0, 1⟩, Real.sqrt 2)

lemma relaxedLowerWitness_mem :
    relaxedLowerWitness ∈ directionalBlowUpChamber := by
  constructor
  · rw [Metric.mem_sphere]
    simp [relaxedLowerWitness, kernelOrigin, planeEmbedding, EuclideanSpace.dist_eq,
      Fin.sum_univ_two]
  · change -Real.sqrt 2 ≤ -Real.sqrt 2 ∧ -Real.sqrt 2 ≤ Real.sqrt 2
    exact ⟨le_rfl, by nlinarith [sqrt_two_nonneg]⟩

lemma relaxedUpperWitness_mem :
    relaxedUpperWitness ∈ directionalBlowUpChamber := by
  constructor
  · rw [Metric.mem_sphere]
    simp [relaxedUpperWitness, kernelOrigin, planeEmbedding, EuclideanSpace.dist_eq,
      Fin.sum_univ_two]
  · change -Real.sqrt 2 ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ Real.sqrt 2
    exact ⟨by nlinarith [sqrt_two_nonneg], le_rfl⟩

theorem relaxedLowerWitness_exact (amplitude : ℝ) :
    forwardBlowUpSq amplitude relaxedLowerWitness = relaxedLowerSq amplitude := by
  simp [forwardBlowUpSq, relaxedLowerWitness, relaxedLowerSq, planeEmbedding]
  ring

theorem relaxedUpperWitness_exact (amplitude : ℝ) :
    forwardBlowUpSq amplitude relaxedUpperWitness = relaxedUpperSq amplitude := by
  simp [forwardBlowUpSq, relaxedUpperWitness, relaxedUpperSq, planeEmbedding]
  ring

theorem relaxed_envelope_exact
    {amplitude : ℝ}
    (hadm : AdmissibleAmplitude amplitude) :
    (∀ point ∈ directionalBlowUpChamber,
      relaxedLowerSq amplitude ≤ forwardBlowUpSq amplitude point ∧
        forwardBlowUpSq amplitude point ≤ relaxedUpperSq amplitude) ∧
    forwardBlowUpSq amplitude relaxedLowerWitness = relaxedLowerSq amplitude ∧
    forwardBlowUpSq amplitude relaxedUpperWitness = relaxedUpperSq amplitude := by
  exact ⟨fun _ hpoint => relaxed_envelope hadm hpoint,
    relaxedLowerWitness_exact amplitude, relaxedUpperWitness_exact amplitude⟩

lemma relaxedLowerSq_pos
    {amplitude : ℝ}
    (hadm : AdmissibleAmplitude amplitude) :
    0 < relaxedLowerSq amplitude := by
  have hbase : 0 < 1 - Real.sqrt 2 * amplitude := sub_pos.mpr hadm.2
  exact sq_pos_of_pos hbase

lemma relaxedUpperSq_pos
    {amplitude : ℝ}
    (hadm : AdmissibleAmplitude amplitude) :
    0 < relaxedUpperSq amplitude := by
  have : 0 < 1 + Real.sqrt 2 * amplitude := by
    nlinarith [mul_nonneg sqrt_two_nonneg hadm.1]
  exact sq_pos_of_pos this

theorem inverseBlowUpSq_bounds
    {amplitude : ℝ}
    (hadm : AdmissibleAmplitude amplitude)
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalBlowUpChamber) :
    (relaxedUpperSq amplitude)⁻¹ ≤ inverseBlowUpSq amplitude point ∧
      inverseBlowUpSq amplitude point ≤ (relaxedLowerSq amplitude)⁻¹ := by
  have henvelope := relaxed_envelope hadm hpoint
  have hlower_pos := relaxedLowerSq_pos hadm
  have hforward_pos : 0 < forwardBlowUpSq amplitude point :=
    lt_of_lt_of_le hlower_pos henvelope.1
  have hupper_pos := relaxedUpperSq_pos hadm
  constructor
  · exact (inv_le_inv₀ hupper_pos hforward_pos).2 henvelope.2
  · exact (inv_le_inv₀ hforward_pos hlower_pos).2 henvelope.1

theorem inverseBlowUpSq_exact_extrema
    (amplitude : ℝ) :
    inverseBlowUpSq amplitude relaxedUpperWitness = (relaxedUpperSq amplitude)⁻¹ ∧
      inverseBlowUpSq amplitude relaxedLowerWitness = (relaxedLowerSq amplitude)⁻¹ := by
  constructor
  · rw [inverseBlowUpSq, relaxedUpperWitness_exact]
  · rw [inverseBlowUpSq, relaxedLowerWitness_exact]

/-- A finite sample's upper inverse record. -/
def inverseSampleMax
    (amplitude : ℝ)
    (sample : Finset BlowUpPoint)
    (hsample : sample.Nonempty) : ℝ :=
  sample.sup' hsample (inverseBlowUpSq amplitude)

/-- Exact relaxed upper inverse envelope; the finite certificate's excess over it
is its measurable tightness gap. -/
def inverseCertificateGap
    (amplitude delta : ℝ)
    (sampleMax : ℝ) : ℝ :=
  sampleMax + inverseBlowUpSqRegularity amplitude * delta -
    (relaxedLowerSq amplitude)⁻¹

theorem inverse_regularity_bound
    {amplitude : ℝ}
    (hadm : AdmissibleAmplitude amplitude)
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalBlowUpChamber)
    (hsecond : second ∈ directionalBlowUpChamber) :
    |inverseBlowUpSq amplitude first - inverseBlowUpSq amplitude second| ≤
      inverseBlowUpSqRegularity amplitude * dist first second := by
  have hreg := forwardBlowUpSq_regularity_bound hadm.1 first hfirst second hsecond
  have henv_first := relaxed_envelope hadm hfirst
  have henv_second := relaxed_envelope hadm hsecond
  have hlower_pos := relaxedLowerSq_pos hadm
  have hf_pos : 0 < forwardBlowUpSq amplitude first :=
    lt_of_lt_of_le hlower_pos henv_first.1
  have hs_pos : 0 < forwardBlowUpSq amplitude second :=
    lt_of_lt_of_le hlower_pos henv_second.1
  have hden : relaxedLowerSq amplitude ^ 2 ≤
      |forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second| := by
    have hraw : relaxedLowerSq amplitude * relaxedLowerSq amplitude ≤
        forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second :=
      mul_le_mul henv_first.1 henv_second.1 (le_of_lt hlower_pos)
        (le_trans (le_of_lt hlower_pos) henv_first.1)
    simpa [pow_two, abs_mul, abs_of_pos hf_pos, abs_of_pos hs_pos] using hraw
  have hden_pos : 0 < |forwardBlowUpSq amplitude first *
      forwardBlowUpSq amplitude second| := abs_pos.mpr (mul_ne_zero hf_pos.ne' hs_pos.ne')
  have hlower_sq_pos : 0 < relaxedLowerSq amplitude ^ 2 := sq_pos_of_pos hlower_pos
  have hnum : |forwardBlowUpSq amplitude second - forwardBlowUpSq amplitude first| ≤
      forwardBlowUpSqRegularity amplitude * dist first second := by
    simpa [abs_sub_comm] using hreg
  have hregularity_nonneg : 0 ≤ forwardBlowUpSqRegularity amplitude := by
    simp [forwardBlowUpSqRegularity]
    positivity
  have htarget_nonneg : 0 ≤
      forwardBlowUpSqRegularity amplitude * dist first second :=
    mul_nonneg hregularity_nonneg dist_nonneg
  have hfrac : |forwardBlowUpSq amplitude second - forwardBlowUpSq amplitude first| /
      |forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second| ≤
      (forwardBlowUpSqRegularity amplitude * dist first second) /
        relaxedLowerSq amplitude ^ 2 := by
    exact div_le_div₀ htarget_nonneg hnum hlower_sq_pos hden
  change |(forwardBlowUpSq amplitude first)⁻¹ -
      (forwardBlowUpSq amplitude second)⁻¹| ≤ _
  rw [inv_sub_inv hf_pos.ne' hs_pos.ne', abs_div]
  calc
    |forwardBlowUpSq amplitude second - forwardBlowUpSq amplitude first| /
          |forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second| ≤
        (forwardBlowUpSqRegularity amplitude * dist first second) /
          relaxedLowerSq amplitude ^ 2 := hfrac
    _ = inverseBlowUpSqRegularity amplitude * dist first second := by
      unfold inverseBlowUpSqRegularity
      field_simp [ne_of_gt hlower_sq_pos]

lemma inverseBlowUpSqRegularity_nonneg
    {amplitude : ℝ}
    (hadm : AdmissibleAmplitude amplitude) :
    0 ≤ inverseBlowUpSqRegularity amplitude := by
  have hnum : 0 ≤ forwardBlowUpSqRegularity amplitude := by
    simp [forwardBlowUpSqRegularity]
    positivity
  have hden : 0 ≤ relaxedLowerSq amplitude ^ 2 := sq_nonneg _
  exact div_nonneg hnum hden

lemma noisySampleUpper_le_of_exact_bounded
    {α : Type*}
    {sample : List (IntrinsicNonradialShearDeltaNet.NoisyUpperReading α)}
    {value : α → ℝ}
    {bound : ℝ}
    (hbound0 : 0 ≤ bound)
    (hexact : ∀ reading ∈ sample,
      reading.measured = value reading.point ∧ reading.error = 0)
    (hbound : ∀ reading ∈ sample, value reading.point ≤ bound) :
    IntrinsicNonradialShearDeltaNet.noisySampleUpper sample ≤ bound := by
  induction sample with
  | nil =>
      simpa [IntrinsicNonradialShearDeltaNet.noisySampleUpper] using hbound0
  | cons reading rest ih =>
      rw [IntrinsicNonradialShearDeltaNet.noisySampleUpper.eq_2]
      apply max_le
      · have hreading := hexact reading (by simp)
        have hv := hbound reading (by simp)
        rw [hreading.1, hreading.2]
        simpa using hv
      · apply ih
        · intro item hitem
          exact hexact item (by simp [hitem])
        · intro item hitem
          exact hbound item (by simp [hitem])

theorem exists_inverseBlowUpSq_finiteCertificate
    {amplitude delta : ℝ}
    (hadm : AdmissibleAmplitude amplitude)
    (hdelta : 0 < delta) :
    ∃ sample,
      IntrinsicNonradialShearDeltaNet.NoisyUpperSampleValid
          (inverseBlowUpSq amplitude) sample ∧
      IntrinsicNonradialShearDeltaNet.DeltaCoverage
          directionalBlowUpChamber sample delta ∧
      IntrinsicNonradialShearClosedCore.SampleInside
          directionalBlowUpChamber sample ∧
      (∀ reading ∈ sample,
        reading.measured = inverseBlowUpSq amplitude reading.point ∧
          reading.error = 0) ∧
      IntrinsicNonradialShearDeltaNet.RegularityCertificate
          directionalBlowUpChamber sample
          (inverseBlowUpSqRegularity amplitude) (inverseBlowUpSq amplitude) ∧
      (∀ point ∈ directionalBlowUpChamber,
        inverseBlowUpSq amplitude point ≤
          IntrinsicNonradialShearDeltaNet.noisySampleUpper sample +
            inverseBlowUpSqRegularity amplitude * delta) ∧
      0 ≤ inverseCertificateGap amplitude delta
        (IntrinsicNonradialShearDeltaNet.noisySampleUpper sample) ∧
      inverseCertificateGap amplitude delta
          (IntrinsicNonradialShearDeltaNet.noisySampleUpper sample) ≤
        inverseBlowUpSqRegularity amplitude * delta := by
  classical
  let value : BlowUpPoint → ℝ := inverseBlowUpSq amplitude
  rcases IntrinsicNonradialShearClosedCore.finiteMetricDeltaNet_of_compact
      directionalBlowUpChamber_compact hdelta with
    ⟨centers, hfinite, hcenters_inside, hcenters_cover⟩
  let centersFinset := hfinite.toFinset
  let sample := centersFinset.toList.map
    (IntrinsicNonradialShearClosedCore.exactUpperReading value)
  have hexact : ∀ reading ∈ sample,
      reading.measured = value reading.point ∧ reading.error = 0 := by
    intro reading hreading
    rcases List.mem_map.mp hreading with ⟨center, hcenter, rfl⟩
    simp [IntrinsicNonradialShearClosedCore.exactUpperReading]
  have hvalid : IntrinsicNonradialShearDeltaNet.NoisyUpperSampleValid value sample := by
    intro reading hreading
    have hreading_exact := hexact reading hreading
    rw [hreading_exact.1, hreading_exact.2]
    norm_num
  have hcoverage : IntrinsicNonradialShearDeltaNet.DeltaCoverage
      directionalBlowUpChamber sample delta := by
    intro point hpoint
    rcases hcenters_cover point hpoint with ⟨center, hcenter, hdist⟩
    refine ⟨IntrinsicNonradialShearClosedCore.exactUpperReading value center, ?_, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨center, ?_, rfl⟩
      simpa [centersFinset] using hcenter
    · simpa [IntrinsicNonradialShearClosedCore.exactUpperReading] using le_of_lt hdist
  have hinside : IntrinsicNonradialShearClosedCore.SampleInside
      directionalBlowUpChamber sample := by
    intro reading hreading
    rcases List.mem_map.mp hreading with ⟨center, hcenter, rfl⟩
    change center ∈ directionalBlowUpChamber
    apply hcenters_inside
    simpa [centersFinset] using hcenter
  have hregular : IntrinsicNonradialShearDeltaNet.RegularityCertificate
      directionalBlowUpChamber sample (inverseBlowUpSqRegularity amplitude) value := by
    intro point hpoint reading hreading
    exact inverse_regularity_bound hadm hpoint (hinside reading hreading)
  have hconstant := inverseBlowUpSqRegularity_nonneg hadm
  have hglobal : ∀ point ∈ directionalBlowUpChamber,
      value point ≤ IntrinsicNonradialShearDeltaNet.noisySampleUpper sample +
        inverseBlowUpSqRegularity amplitude * delta := by
    intro point hpoint
    exact IntrinsicNonradialShearDeltaNet.global_le_noisySampleUpper_add_regularity
      hconstant hvalid hcoverage hregular point hpoint
  have hupper_pos : 0 ≤ (relaxedLowerSq amplitude)⁻¹ :=
    le_of_lt (inv_pos.mpr (relaxedLowerSq_pos hadm))
  have hsample_upper : IntrinsicNonradialShearDeltaNet.noisySampleUpper sample ≤
      (relaxedLowerSq amplitude)⁻¹ := by
    apply noisySampleUpper_le_of_exact_bounded hupper_pos hexact
    intro reading hreading
    exact (inverseBlowUpSq_bounds hadm (hinside reading hreading)).2
  have hglobal_at_pole := hglobal relaxedLowerWitness relaxedLowerWitness_mem
  have hpole := (inverseBlowUpSq_exact_extrema amplitude).2
  have hgap_nonneg : 0 ≤ inverseCertificateGap amplitude delta
      (IntrinsicNonradialShearDeltaNet.noisySampleUpper sample) := by
    change inverseBlowUpSq amplitude relaxedLowerWitness ≤ _ at hglobal_at_pole
    rw [hpole] at hglobal_at_pole
    simp only [inverseCertificateGap]
    linarith
  have hgap_upper : inverseCertificateGap amplitude delta
        (IntrinsicNonradialShearDeltaNet.noisySampleUpper sample) ≤
      inverseBlowUpSqRegularity amplitude * delta := by
    simp only [inverseCertificateGap]
    linarith
  exact ⟨sample, hvalid, hcoverage, hinside, hexact, hregular, hglobal,
    hgap_nonneg, hgap_upper⟩

end

end BoundaryOfSelf.IntrinsicNonradialShearDiagonalBlowUpInverse
