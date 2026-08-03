import IntrinsicNonradialShearRealizableClosure

open scoped Topology RealInnerProductSpace
open Set Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearRealizableCertificate

noncomputable section

open StandardHausdorffMetricBridge
open IntrinsicNonradialShearKernelSharp
open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearDiagonalBlowUpInverse
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearRealizableClosure
open IntrinsicNonradialShearDeltaNet
open IntrinsicNonradialShearClosedCore

/-! ## IF-BS-22F-F8C16: exact-domain finite certificates -/

/-- A lower square certificate derived from the directional diamond itself. -/
def diamondLowerSq (amplitude : ℝ) : ℝ :=
  (1 - amplitude) ^ 2 / 2

/-- Keep whichever independently proved lower certificate is stronger. -/
def certifiedDiamondLowerSq (amplitude : ℝ) : ℝ :=
  max (relaxedLowerSq amplitude) (diamondLowerSq amplitude)

/-- Reciprocal modulus obtained from the certified lower square on the exact
realizable chamber. -/
def certifiedDiamondInverseRegularity (amplitude : ℝ) : ℝ :=
  forwardBlowUpSqRegularity amplitude /
    (certifiedDiamondLowerSq amplitude) ^ 2

def relaxedInverseMeshTerm (amplitude delta : ℝ) : ℝ :=
  inverseBlowUpSqRegularity amplitude * delta

def certifiedDiamondInverseMeshTerm (amplitude delta : ℝ) : ℝ :=
  certifiedDiamondInverseRegularity amplitude * delta

lemma admissibleAmplitude_lt_one
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude) :
    amplitude < 1 := by
  have hsqrt_one : 1 ≤ Real.sqrt 2 := by
    nlinarith [sqrt_two_nonneg, sqrt_two_sq]
  have hscaled : amplitude ≤ Real.sqrt 2 * amplitude := by
    nlinarith [hadm.1]
  linarith [hadm.2]

lemma diamond_unit_and_slope
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalDiamondBand) :
    point.1.ofLp 0 ^ 2 + point.1.ofLp 1 ^ 2 = 1 ∧
      |point.2| ≤ |point.1.ofLp 0| + |point.1.ofLp 1| := by
  rw [directionalDiamondBand] at hpoint
  exact ⟨(chamber_unit_and_slope hpoint.1).1, hpoint.2⟩

lemma diamond_width_le_sqrt_two
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalDiamondBand) :
    |point.1.ofLp 0| + |point.1.ofLp 1| ≤ Real.sqrt 2 := by
  have hunit := (diamond_unit_and_slope hpoint).1
  have hsum0 :
      0 ≤ |point.1.ofLp 0| + |point.1.ofLp 1| := by positivity
  have hsquare :
      (|point.1.ofLp 0| + |point.1.ofLp 1|) ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg (|point.1.ofLp 0| - |point.1.ofLp 1|),
      sq_abs (point.1.ofLp 0), sq_abs (point.1.ofLp 1)]
  nlinarith [sqrt_two_nonneg, sqrt_two_sq]

lemma diamond_mem_relaxedChamber
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalDiamondBand) :
    point ∈ directionalBlowUpChamber := by
  rw [directionalDiamondBand] at hpoint
  exact hpoint.1

theorem diamond_lower_certificate
    {amplitude : ℝ}
    (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1)
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalDiamondBand) :
    diamondLowerSq amplitude ≤ forwardBlowUpSq amplitude point := by
  rcases diamond_unit_and_slope hpoint with ⟨hunit, hslope⟩
  let x : ℝ := point.1.ofLp 0
  let y : ℝ := point.1.ofLp 1
  let s : ℝ := point.2
  let z : ℝ := y + amplitude * s
  have haUpper : amplitude ≤ 1 := le_of_lt ha1
  have hfactor0 : 0 ≤ 1 - amplitude := sub_nonneg.mpr haUpper
  have hyBridge : |y| ≤ |z| + amplitude * (|x| + |y|) := by
    calc
      |y| = |z - amplitude * s| := by
        congr 1
        dsimp [z]
        ring
      _ ≤ |z| + |amplitude * s| := abs_sub _ _
      _ = |z| + amplitude * |s| := by
        rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ |z| + amplitude * (|x| + |y|) := by
        simpa [x, y, s] using
          add_le_add_left (mul_le_mul_of_nonneg_left hslope ha0) |z|
  have hlinear : (1 - amplitude) * |y| ≤ |z| + amplitude * |x| := by
    nlinarith
  have hleft0 : 0 ≤ (1 - amplitude) * |y| :=
    mul_nonneg hfactor0 (abs_nonneg y)
  have hright0 : 0 ≤ |z| + amplitude * |x| := by positivity
  have hsquared :
      ((1 - amplitude) * |y|) ^ 2 ≤
        (|z| + amplitude * |x|) ^ 2 :=
    (sq_le_sq₀ hleft0 hright0).2 hlinear
  have hrecover :
      (1 - amplitude) ^ 2 * y ^ 2 ≤
        2 * z ^ 2 + 2 * amplitude ^ 2 * x ^ 2 := by
    nlinarith [hsquared, sq_nonneg (|z| - amplitude * |x|),
      sq_abs x, sq_abs y, sq_abs z]
  have hpoly : (amplitude - 1) * (3 * amplitude + 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by nlinarith)
  have hcoefficient :
      (1 - amplitude) ^ 2 + 2 * amplitude ^ 2 ≤ 2 := by
    nlinarith
  have hcoefficientX :
      ((1 - amplitude) ^ 2 + 2 * amplitude ^ 2) * x ^ 2 ≤
        2 * x ^ 2 :=
    mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg x)
  have hscaled :
      (1 - amplitude) ^ 2 ≤ 2 * (x ^ 2 + z ^ 2) := by
    dsimp [x, y, s] at hunit hslope
    change x ^ 2 + y ^ 2 = 1 at hunit
    nlinarith
  dsimp [diamondLowerSq, forwardBlowUpSq, x, y, s, z] at *
  linarith

theorem certifiedDiamond_lower_certificate
    {amplitude : ℝ}
    (hadm : AdmissibleAmplitude amplitude)
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalDiamondBand) :
    certifiedDiamondLowerSq amplitude ≤
      forwardBlowUpSq amplitude point := by
  rw [certifiedDiamondLowerSq]
  apply max_le
  · exact (relaxed_envelope hadm (diamond_mem_relaxedChamber hpoint)).1
  · exact diamond_lower_certificate hadm.1
      (admissibleAmplitude_lt_one hadm) hpoint

lemma diamondLowerSq_pos
    {amplitude : ℝ} (ha1 : amplitude < 1) :
    0 < diamondLowerSq amplitude := by
  unfold diamondLowerSq
  positivity

lemma certifiedDiamondLowerSq_pos
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude) :
    0 < certifiedDiamondLowerSq amplitude := by
  exact lt_of_lt_of_le (relaxedLowerSq_pos hadm)
    (le_max_left _ _)

theorem certifiedDiamond_inverse_bounds
    {amplitude : ℝ}
    (hadm : AdmissibleAmplitude amplitude)
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalDiamondBand) :
    (relaxedUpperSq amplitude)⁻¹ ≤ inverseBlowUpSq amplitude point ∧
      inverseBlowUpSq amplitude point ≤
        (certifiedDiamondLowerSq amplitude)⁻¹ := by
  have hrelaxed := relaxed_envelope hadm (diamond_mem_relaxedChamber hpoint)
  have hlower := certifiedDiamond_lower_certificate hadm hpoint
  have hcert_pos := certifiedDiamondLowerSq_pos hadm
  have hforward_pos : 0 < forwardBlowUpSq amplitude point :=
    lt_of_lt_of_le hcert_pos hlower
  have hupper_pos := relaxedUpperSq_pos hadm
  constructor
  · exact (inv_le_inv₀ hupper_pos hforward_pos).2 hrelaxed.2
  · exact (inv_le_inv₀ hforward_pos hcert_pos).2 hlower

theorem certifiedDiamond_inverse_regularity_bound
    {amplitude : ℝ}
    (hadm : AdmissibleAmplitude amplitude)
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand) :
    |inverseBlowUpSq amplitude first - inverseBlowUpSq amplitude second| ≤
      certifiedDiamondInverseRegularity amplitude * dist first second := by
  have hreg := forwardBlowUpSq_regularity_bound hadm.1 first
    (diamond_mem_relaxedChamber hfirst) second
    (diamond_mem_relaxedChamber hsecond)
  have henv_first := certifiedDiamond_lower_certificate hadm hfirst
  have henv_second := certifiedDiamond_lower_certificate hadm hsecond
  have hlower_pos := certifiedDiamondLowerSq_pos hadm
  have hf_pos : 0 < forwardBlowUpSq amplitude first :=
    lt_of_lt_of_le hlower_pos henv_first
  have hs_pos : 0 < forwardBlowUpSq amplitude second :=
    lt_of_lt_of_le hlower_pos henv_second
  have hden : certifiedDiamondLowerSq amplitude ^ 2 ≤
      |forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second| := by
    have hraw : certifiedDiamondLowerSq amplitude *
        certifiedDiamondLowerSq amplitude ≤
          forwardBlowUpSq amplitude first *
            forwardBlowUpSq amplitude second :=
      mul_le_mul henv_first henv_second (le_of_lt hlower_pos)
        (le_trans (le_of_lt hlower_pos) henv_first)
    simpa [pow_two, abs_mul, abs_of_pos hf_pos, abs_of_pos hs_pos] using hraw
  have hden_pos : 0 < |forwardBlowUpSq amplitude first *
      forwardBlowUpSq amplitude second| :=
    abs_pos.mpr (mul_ne_zero hf_pos.ne' hs_pos.ne')
  have hlower_sq_pos : 0 < certifiedDiamondLowerSq amplitude ^ 2 :=
    sq_pos_of_pos hlower_pos
  have hnum : |forwardBlowUpSq amplitude second -
      forwardBlowUpSq amplitude first| ≤
        forwardBlowUpSqRegularity amplitude * dist first second := by
    simpa [abs_sub_comm] using hreg
  have hregularity_nonneg : 0 ≤ forwardBlowUpSqRegularity amplitude := by
    simp [forwardBlowUpSqRegularity]
    positivity
  have htarget_nonneg : 0 ≤
      forwardBlowUpSqRegularity amplitude * dist first second :=
    mul_nonneg hregularity_nonneg dist_nonneg
  have hfrac : |forwardBlowUpSq amplitude second -
        forwardBlowUpSq amplitude first| /
      |forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second| ≤
        (forwardBlowUpSqRegularity amplitude * dist first second) /
          certifiedDiamondLowerSq amplitude ^ 2 := by
    exact div_le_div₀ htarget_nonneg hnum hlower_sq_pos hden
  change |(forwardBlowUpSq amplitude first)⁻¹ -
      (forwardBlowUpSq amplitude second)⁻¹| ≤ _
  rw [inv_sub_inv hf_pos.ne' hs_pos.ne', abs_div]
  calc
    |forwardBlowUpSq amplitude second - forwardBlowUpSq amplitude first| /
          |forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second| ≤
        (forwardBlowUpSqRegularity amplitude * dist first second) /
          certifiedDiamondLowerSq amplitude ^ 2 := hfrac
    _ = certifiedDiamondInverseRegularity amplitude * dist first second := by
      unfold certifiedDiamondInverseRegularity
      field_simp [ne_of_gt hlower_sq_pos]

lemma certifiedDiamondInverseRegularity_nonneg
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude) :
    0 ≤ certifiedDiamondInverseRegularity amplitude := by
  unfold certifiedDiamondInverseRegularity
  exact div_nonneg (forwardBlowUpSqRegularity_nonneg hadm.1)
    (sq_nonneg _)

theorem certifiedDiamondInverseRegularity_le_relaxed
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude) :
    certifiedDiamondInverseRegularity amplitude ≤
      inverseBlowUpSqRegularity amplitude := by
  have hnum : 0 ≤ forwardBlowUpSqRegularity amplitude :=
    forwardBlowUpSqRegularity_nonneg hadm.1
  have hold_pos := relaxedLowerSq_pos hadm
  have hnew_pos := certifiedDiamondLowerSq_pos hadm
  have hlower : relaxedLowerSq amplitude ≤
      certifiedDiamondLowerSq amplitude := le_max_left _ _
  have hsquare : relaxedLowerSq amplitude ^ 2 ≤
      certifiedDiamondLowerSq amplitude ^ 2 := by nlinarith
  unfold certifiedDiamondInverseRegularity inverseBlowUpSqRegularity
  exact div_le_div_of_nonneg_left hnum (sq_pos_of_pos hold_pos) hsquare

theorem certifiedDiamondInverseMeshTerm_le_relaxed
    {amplitude delta : ℝ}
    (hadm : AdmissibleAmplitude amplitude) (hdelta : 0 ≤ delta) :
    certifiedDiamondInverseMeshTerm amplitude delta ≤
      relaxedInverseMeshTerm amplitude delta := by
  unfold certifiedDiamondInverseMeshTerm relaxedInverseMeshTerm
  exact mul_le_mul_of_nonneg_right
    (certifiedDiamondInverseRegularity_le_relaxed hadm) hdelta

theorem half_amplitude_diamond_stronger :
    relaxedLowerSq (1 / 2 : ℝ) < diamondLowerSq (1 / 2 : ℝ) := by
  unfold relaxedLowerSq diamondLowerSq
  nlinarith [sqrt_two_nonneg, sqrt_two_sq]

theorem half_amplitude_certifiedLower_exact :
    certifiedDiamondLowerSq (1 / 2 : ℝ) = diamondLowerSq (1 / 2 : ℝ) := by
  unfold certifiedDiamondLowerSq
  exact max_eq_right (le_of_lt half_amplitude_diamond_stronger)

lemma half_amplitude_admissible : AdmissibleAmplitude (1 / 2 : ℝ) := by
  constructor
  · norm_num
  · nlinarith [sqrt_two_nonneg, sqrt_two_sq]

theorem half_amplitude_inverseRegularity_strict :
    certifiedDiamondInverseRegularity (1 / 2 : ℝ) <
      inverseBlowUpSqRegularity (1 / 2 : ℝ) := by
  rw [certifiedDiamondInverseRegularity, inverseBlowUpSqRegularity,
    half_amplitude_certifiedLower_exact]
  have hnum : 0 < forwardBlowUpSqRegularity (1 / 2 : ℝ) := by
    norm_num [forwardBlowUpSqRegularity]
  have hold := relaxedLowerSq_pos half_amplitude_admissible
  have hnew := diamondLowerSq_pos
    (admissibleAmplitude_lt_one half_amplitude_admissible)
  have hsquare : relaxedLowerSq (1 / 2 : ℝ) ^ 2 <
      diamondLowerSq (1 / 2 : ℝ) ^ 2 := by
    nlinarith [half_amplitude_diamond_stronger]
  rw [div_lt_div_iff₀ (sq_pos_of_pos hnew) (sq_pos_of_pos hold)]
  exact mul_lt_mul_of_pos_left hsquare hnum

theorem half_amplitude_inverseMeshTerm_strict
    {delta : ℝ} (hdelta : 0 < delta) :
    certifiedDiamondInverseMeshTerm (1 / 2 : ℝ) delta <
      relaxedInverseMeshTerm (1 / 2 : ℝ) delta := by
  unfold certifiedDiamondInverseMeshTerm relaxedInverseMeshTerm
  exact mul_lt_mul_of_pos_right half_amplitude_inverseRegularity_strict hdelta

theorem forward_diamond_regularity_bound
    {amplitude : ℝ} (ha : 0 ≤ amplitude) :
    ∀ first ∈ directionalDiamondBand,
      ∀ second ∈ directionalDiamondBand,
        |forwardBlowUpSq amplitude first -
            forwardBlowUpSq amplitude second| ≤
          forwardBlowUpSqRegularity amplitude * dist first second := by
  intro first hfirst second hsecond
  exact forwardBlowUpSq_regularity_bound ha first
    (diamond_mem_relaxedChamber hfirst) second
    (diamond_mem_relaxedChamber hsecond)

theorem exists_forward_diamond_finiteCertificate
    {amplitude delta : ℝ}
    (ha : 0 ≤ amplitude) (hdelta : 0 < delta) :
    ∃ sample : List (NoisyUpperReading BlowUpPoint),
      NoisyUpperSampleValid (forwardBlowUpSq amplitude) sample ∧
      DeltaCoverage directionalDiamondBand sample delta ∧
      SampleInside directionalDiamondBand sample ∧
      RegularityCertificate directionalDiamondBand sample
        (forwardBlowUpSqRegularity amplitude) (forwardBlowUpSq amplitude) ∧
      ∀ point, point ∈ directionalDiamondBand →
        forwardBlowUpSq amplitude point ≤
          noisySampleUpper sample +
            forwardBlowUpSqRegularity amplitude * delta := by
  rcases compact_exists_finite_exactSample
      directionalDiamondBand_compact hdelta
      (forwardBlowUpSq amplitude) with
    ⟨sample, hvalid, hcoverage, hinside⟩
  have hregular : RegularityCertificate directionalDiamondBand sample
      (forwardBlowUpSqRegularity amplitude) (forwardBlowUpSq amplitude) := by
    intro point hpoint reading hreading
    exact forward_diamond_regularity_bound ha point hpoint
      reading.point (hinside reading hreading)
  refine ⟨sample, hvalid, hcoverage, hinside, hregular, ?_⟩
  intro point hpoint
  exact global_le_noisySampleUpper_add_regularity
    (forwardBlowUpSqRegularity_nonneg ha)
    hvalid hcoverage hregular point hpoint

theorem exists_inverse_diamond_finiteCertificate
    {amplitude delta : ℝ}
    (hadm : AdmissibleAmplitude amplitude) (hdelta : 0 < delta) :
    ∃ sample : List (NoisyUpperReading BlowUpPoint),
      NoisyUpperSampleValid (inverseBlowUpSq amplitude) sample ∧
      DeltaCoverage directionalDiamondBand sample delta ∧
      SampleInside directionalDiamondBand sample ∧
      RegularityCertificate directionalDiamondBand sample
        (certifiedDiamondInverseRegularity amplitude)
        (inverseBlowUpSq amplitude) ∧
      ∀ point, point ∈ directionalDiamondBand →
        inverseBlowUpSq amplitude point ≤
          noisySampleUpper sample +
            certifiedDiamondInverseMeshTerm amplitude delta := by
  rcases compact_exists_finite_exactSample
      directionalDiamondBand_compact hdelta
      (inverseBlowUpSq amplitude) with
    ⟨sample, hvalid, hcoverage, hinside⟩
  have hregular : RegularityCertificate directionalDiamondBand sample
      (certifiedDiamondInverseRegularity amplitude)
      (inverseBlowUpSq amplitude) := by
    intro point hpoint reading hreading
    exact certifiedDiamond_inverse_regularity_bound hadm hpoint
      (hinside reading hreading)
  refine ⟨sample, hvalid, hcoverage, hinside, hregular, ?_⟩
  intro point hpoint
  simpa [certifiedDiamondInverseMeshTerm] using
    global_le_noisySampleUpper_add_regularity
      (certifiedDiamondInverseRegularity_nonneg hadm)
      hvalid hcoverage hregular point hpoint

end

end BoundaryOfSelf.IntrinsicNonradialShearRealizableCertificate
