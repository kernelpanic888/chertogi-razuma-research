import IntrinsicNonradialShearSharpEnvelope

open scoped Topology RealInnerProductSpace
open Set Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearSlopeEnvelope

noncomputable section

open StandardHausdorffMetricBridge
open LocalSegmentRealCompletion
open IntrinsicNonradialShearExactSupport
open IntrinsicNonradialShearSpectralMap
open IntrinsicNonradialShearKernelSharp
open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearDiagonalBlowUpInverse
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearRealizableClosure
open IntrinsicNonradialShearRealizableCertificate
open IntrinsicNonradialShearSharpEnvelope

/-! ## IF-BS-22F-F8C18: exact slope envelope and improved regularity -/

def exactSlopeRadius (amplitude : ℝ) : ℝ :=
  Real.sqrt (amplitude ^ 2 + (1 + amplitude) ^ 2)

lemma slopeRadicand_pos
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    0 < amplitude ^ 2 + (1 + amplitude) ^ 2 := by
  nlinarith [sq_nonneg amplitude]

lemma exactSlopeRadius_pos
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    0 < exactSlopeRadius amplitude := by
  exact Real.sqrt_pos.2 (slopeRadicand_pos ha0)

lemma exactSlopeRadius_sq
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    exactSlopeRadius amplitude ^ 2 =
      amplitude ^ 2 + (1 + amplitude) ^ 2 := by
  rw [exactSlopeRadius, Real.sq_sqrt (le_of_lt (slopeRadicand_pos ha0))]

theorem exactSlopeRadius_bound
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude)
    {point : BlowUpPoint} (hpoint : point ∈ directionalDiamondBand) :
    |point.1.ofLp 1 + amplitude * point.2| ≤ exactSlopeRadius amplitude := by
  rcases diamond_unit_and_slope hpoint with ⟨hunit, hslope⟩
  let x : ℝ := point.1.ofLp 0
  let y : ℝ := point.1.ofLp 1
  let s : ℝ := point.2
  let X : ℝ := |x|
  let Y : ℝ := |y|
  let z : ℝ := y + amplitude * s
  have hlinear : |z| ≤ amplitude * X + (1 + amplitude) * Y := by
    calc
      |z| = |y + amplitude * s| := rfl
      _ ≤ |y| + |amplitude * s| := abs_add_le _ _
      _ = Y + amplitude * |s| := by
        dsimp [Y]
        rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ Y + amplitude * (X + Y) := by
        simpa [X, Y, s, add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_left hslope ha0) Y
      _ = amplitude * X + (1 + amplitude) * Y := by ring
  have hunitAbs : X ^ 2 + Y ^ 2 = 1 := by
    dsimp [X, Y, x, y]
    simpa [sq_abs] using hunit
  have hcombination0 : 0 ≤ amplitude * X + (1 + amplitude) * Y := by
    dsimp [X, Y]
    positivity
  have hcombinationSq :
      (amplitude * X + (1 + amplitude) * Y) ^ 2 ≤
        amplitude ^ 2 + (1 + amplitude) ^ 2 := by
    nlinarith [sq_nonneg ((1 + amplitude) * X - amplitude * Y)]
  have hradius0 : 0 ≤ exactSlopeRadius amplitude :=
    le_of_lt (exactSlopeRadius_pos ha0)
  have hradiusSq := exactSlopeRadius_sq ha0
  have hcombination :
      amplitude * X + (1 + amplitude) * Y ≤ exactSlopeRadius amplitude := by
    nlinarith
  exact hlinear.trans hcombination

def slopeExtremizingDirection (amplitude : ℝ) : AmbientPlane :=
  normalizedPositiveDirection amplitude (1 + amplitude)

def slopeEnvelopeWitness (amplitude : ℝ) : BlowUpPoint :=
  (slopeExtremizingDirection amplitude,
    (slopeExtremizingDirection amplitude).ofLp 0 +
      (slopeExtremizingDirection amplitude).ofLp 1)

lemma slope_raw_sum_pos
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    0 < amplitude ^ 2 + (1 + amplitude) ^ 2 :=
  slopeRadicand_pos ha0

lemma slope_direction_coordinates_nonneg
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    0 ≤ (slopeExtremizingDirection amplitude).ofLp 0 ∧
      0 ≤ (slopeExtremizingDirection amplitude).ofLp 1 := by
  have hsum := slope_raw_sum_pos ha0
  have hnorm := le_of_lt (rawNorm_pos hsum)
  constructor
  · simp [slopeExtremizingDirection, normalizedPositiveDirection,
      planeEmbedding]
    exact div_nonneg ha0 hnorm
  · simp [slopeExtremizingDirection, normalizedPositiveDirection,
      planeEmbedding]
    exact div_nonneg (by linarith) hnorm

lemma slopeEnvelopeWitness_mem
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    slopeEnvelopeWitness amplitude ∈ directionalDiamondBand := by
  have hsum := slope_raw_sum_pos ha0
  have hsphere := normalizedPositiveDirection_mem_sphere hsum
  have hwidth := normalizedPositiveDirection_width_le_sqrt_two hsum
  rcases slope_direction_coordinates_nonneg ha0 with ⟨hx, hy⟩
  have hslope :
      |(slopeEnvelopeWitness amplitude).2| =
        |(slopeExtremizingDirection amplitude).ofLp 0| +
          |(slopeExtremizingDirection amplitude).ofLp 1| := by
    simp [slopeEnvelopeWitness, abs_of_nonneg hx, abs_of_nonneg hy,
      abs_of_nonneg (add_nonneg hx hy)]
  rw [directionalDiamondBand]
  constructor
  · refine ⟨hsphere, ?_⟩
    exact abs_le.mp (hslope.le.trans hwidth)
  · exact hslope.le

theorem slopeEnvelopeWitness_exact
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    |(slopeEnvelopeWitness amplitude).1.ofLp 1 +
        amplitude * (slopeEnvelopeWitness amplitude).2| =
      exactSlopeRadius amplitude := by
  have hsum := slope_raw_sum_pos ha0
  have hnorm_pos := rawNorm_pos hsum
  have hnorm_ne : rawNorm amplitude (1 + amplitude) ≠ 0 :=
    ne_of_gt hnorm_pos
  have hnorm_sq := rawNorm_sq (le_of_lt hsum)
  have hradius_eq :
      rawNorm amplitude (1 + amplitude) = exactSlopeRadius amplitude := rfl
  have hvalue :
      (slopeEnvelopeWitness amplitude).1.ofLp 1 +
          amplitude * (slopeEnvelopeWitness amplitude).2 =
        exactSlopeRadius amplitude := by
    simp [slopeEnvelopeWitness, slopeExtremizingDirection,
      normalizedPositiveDirection, planeEmbedding]
    field_simp [hnorm_ne]
    rw [← hradius_eq]
    nlinarith
  rw [hvalue, abs_of_pos (exactSlopeRadius_pos ha0)]

theorem exactSlopeRadius_isSharp
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    IsGreatest
      ((fun point : BlowUpPoint =>
        |point.1.ofLp 1 + amplitude * point.2|) '' directionalDiamondBand)
      (exactSlopeRadius amplitude) := by
  constructor
  · exact ⟨slopeEnvelopeWitness amplitude, slopeEnvelopeWitness_mem ha0,
      slopeEnvelopeWitness_exact ha0⟩
  · rintro value ⟨point, hpoint, rfl⟩
    exact exactSlopeRadius_bound ha0 hpoint

def slopeEnvelopeForwardRegularity (amplitude : ℝ) : ℝ :=
  2 + 2 * (1 + amplitude) * exactSlopeRadius amplitude

lemma slopeEnvelopeForwardRegularity_nonneg
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    0 ≤ slopeEnvelopeForwardRegularity amplitude := by
  unfold slopeEnvelopeForwardRegularity
  have hr0 : 0 ≤ exactSlopeRadius amplitude :=
    le_of_lt (exactSlopeRadius_pos ha0)
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + amplitude) hr0]

theorem slopeEnvelope_forward_regularity_bound
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    ∀ first ∈ directionalDiamondBand,
      ∀ second ∈ directionalDiamondBand,
        |forwardBlowUpSq amplitude first -
            forwardBlowUpSq amplitude second| ≤
          slopeEnvelopeForwardRegularity amplitude * dist first second := by
  intro first hfirst second hsecond
  let x₁ : ℝ := first.1.ofLp 0
  let y₁ : ℝ := first.1.ofLp 1
  let s₁ : ℝ := first.2
  let x₂ : ℝ := second.1.ofLp 0
  let y₂ : ℝ := second.1.ofLp 1
  let s₂ : ℝ := second.2
  let v₁ : ℝ := y₁ + amplitude * s₁
  let v₂ : ℝ := y₂ + amplitude * s₂
  let D : ℝ := dist first second
  let R : ℝ := exactSlopeRadius amplitude
  have hD0 : 0 ≤ D := dist_nonneg
  have hR0 : 0 ≤ R := le_of_lt (exactSlopeRadius_pos ha0)
  have hx₁ : |x₁| ≤ 1 :=
    direction_x_abs_le_one (diamond_mem_relaxedChamber hfirst).1
  have hx₂ : |x₂| ≤ 1 :=
    direction_x_abs_le_one (diamond_mem_relaxedChamber hsecond).1
  have hv₁ : |v₁| ≤ R := exactSlopeRadius_bound ha0 hfirst
  have hv₂ : |v₂| ≤ R := exactSlopeRadius_bound ha0 hsecond
  have hxDifference : |x₁ - x₂| ≤ D :=
    blowUp_x_sub_abs_le_dist first second
  have hyDifference : |y₁ - y₂| ≤ D :=
    blowUp_y_sub_abs_le_dist first second
  have hsDifference : |s₁ - s₂| ≤ D :=
    blowUp_slope_sub_abs_le_dist first second
  have hvDifference : |v₁ - v₂| ≤ (1 + amplitude) * D := by
    calc
      |v₁ - v₂| = |(y₁ - y₂) + amplitude * (s₁ - s₂)| := by
        congr 1
        dsimp [v₁, v₂]
        ring
      _ ≤ |y₁ - y₂| + |amplitude * (s₁ - s₂)| := abs_add_le _ _
      _ = |y₁ - y₂| + amplitude * |s₁ - s₂| := by
        rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ D + amplitude * D := by
        exact add_le_add hyDifference
          (mul_le_mul_of_nonneg_left hsDifference ha0)
      _ = (1 + amplitude) * D := by ring
  have hxSum : |x₁ + x₂| ≤ 2 := by
    calc
      |x₁ + x₂| ≤ |x₁| + |x₂| := abs_add_le _ _
      _ ≤ 2 := by linarith
  have hvSum : |v₁ + v₂| ≤ 2 * R := by
    calc
      |v₁ + v₂| ≤ |v₁| + |v₂| := abs_add_le _ _
      _ ≤ 2 * R := by linarith
  have hxSquareDifference : |x₁ ^ 2 - x₂ ^ 2| ≤ 2 * D := by
    rw [show x₁ ^ 2 - x₂ ^ 2 = (x₁ - x₂) * (x₁ + x₂) by ring]
    rw [abs_mul]
    have hmul := mul_le_mul hxDifference hxSum (abs_nonneg _) hD0
    nlinarith
  have hvRight0 : 0 ≤ (1 + amplitude) * D :=
    mul_nonneg (by linarith) hD0
  have hvSquareDifference :
      |v₁ ^ 2 - v₂ ^ 2| ≤
        2 * (1 + amplitude) * R * D := by
    rw [show v₁ ^ 2 - v₂ ^ 2 = (v₁ - v₂) * (v₁ + v₂) by ring]
    rw [abs_mul]
    have hmul := mul_le_mul hvDifference hvSum (abs_nonneg _) hvRight0
    nlinarith
  calc
    |forwardBlowUpSq amplitude first - forwardBlowUpSq amplitude second| =
        |(x₁ ^ 2 - x₂ ^ 2) + (v₁ ^ 2 - v₂ ^ 2)| := by
          congr 1
          dsimp [forwardBlowUpSq, x₁, x₂, y₁, y₂, s₁, s₂, v₁, v₂]
          ring
    _ ≤ |x₁ ^ 2 - x₂ ^ 2| + |v₁ ^ 2 - v₂ ^ 2| := abs_add_le _ _
    _ ≤ 2 * D + 2 * (1 + amplitude) * R * D :=
      add_le_add hxSquareDifference hvSquareDifference
    _ = slopeEnvelopeForwardRegularity amplitude * dist first second := by
      dsimp [slopeEnvelopeForwardRegularity, D, R]
      ring

lemma exactSlopeRadius_lt_two
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    exactSlopeRadius amplitude < 2 * (1 + amplitude) := by
  have hr0 : 0 ≤ exactSlopeRadius amplitude :=
    le_of_lt (exactSlopeRadius_pos ha0)
  have hright : 0 < 2 * (1 + amplitude) := by linarith
  have hrsq := exactSlopeRadius_sq ha0
  nlinarith [sq_nonneg amplitude]

theorem slopeEnvelopeForwardRegularity_lt_coarse
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    slopeEnvelopeForwardRegularity amplitude <
      forwardBlowUpSqRegularity amplitude := by
  have hr := exactSlopeRadius_lt_two ha0
  unfold slopeEnvelopeForwardRegularity forwardBlowUpSqRegularity
  nlinarith

def slopeEnvelopeInverseRegularity (amplitude : ℝ) : ℝ :=
  slopeEnvelopeForwardRegularity amplitude /
    (exactDiamondLowerSq amplitude) ^ 2

def slopeEnvelopeInverseMeshTerm (amplitude delta : ℝ) : ℝ :=
  slopeEnvelopeInverseRegularity amplitude * delta

def slopeEnvelopeInverseCertificateGap
    (amplitude delta sampleMax : ℝ) : ℝ :=
  sampleMax + slopeEnvelopeInverseMeshTerm amplitude delta -
    (exactDiamondLowerSq amplitude)⁻¹

theorem slopeEnvelope_inverse_regularity_bound
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude)
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand) :
    |inverseBlowUpSq amplitude first - inverseBlowUpSq amplitude second| ≤
      slopeEnvelopeInverseRegularity amplitude * dist first second := by
  have hreg := slopeEnvelope_forward_regularity_bound hadm.1
    first hfirst second hsecond
  have henv_first := exactDiamond_lower_bound hadm.1
    (admissibleAmplitude_lt_one hadm) hfirst
  have henv_second := exactDiamond_lower_bound hadm.1
    (admissibleAmplitude_lt_one hadm) hsecond
  have hlower_pos := exactDiamondLowerSq_pos hadm.1
    (admissibleAmplitude_lt_one hadm)
  have hf_pos : 0 < forwardBlowUpSq amplitude first :=
    lt_of_lt_of_le hlower_pos henv_first
  have hs_pos : 0 < forwardBlowUpSq amplitude second :=
    lt_of_lt_of_le hlower_pos henv_second
  have hden : exactDiamondLowerSq amplitude ^ 2 ≤
      |forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second| := by
    have hraw : exactDiamondLowerSq amplitude * exactDiamondLowerSq amplitude ≤
        forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second :=
      mul_le_mul henv_first henv_second (le_of_lt hlower_pos)
        (le_trans (le_of_lt hlower_pos) henv_first)
    simpa [pow_two, abs_mul, abs_of_pos hf_pos, abs_of_pos hs_pos] using hraw
  have hden_pos : 0 < |forwardBlowUpSq amplitude first *
      forwardBlowUpSq amplitude second| :=
    abs_pos.mpr (mul_ne_zero hf_pos.ne' hs_pos.ne')
  have hlower_sq_pos : 0 < exactDiamondLowerSq amplitude ^ 2 :=
    sq_pos_of_pos hlower_pos
  have hnum : |forwardBlowUpSq amplitude second -
      forwardBlowUpSq amplitude first| ≤
        slopeEnvelopeForwardRegularity amplitude * dist first second := by
    simpa [abs_sub_comm] using hreg
  have hregularity_nonneg : 0 ≤ slopeEnvelopeForwardRegularity amplitude :=
    slopeEnvelopeForwardRegularity_nonneg hadm.1
  have htarget_nonneg : 0 ≤
      slopeEnvelopeForwardRegularity amplitude * dist first second :=
    mul_nonneg hregularity_nonneg dist_nonneg
  have hfrac : |forwardBlowUpSq amplitude second -
        forwardBlowUpSq amplitude first| /
      |forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second| ≤
        (slopeEnvelopeForwardRegularity amplitude * dist first second) /
          exactDiamondLowerSq amplitude ^ 2 :=
    div_le_div₀ htarget_nonneg hnum hlower_sq_pos hden
  change |(forwardBlowUpSq amplitude first)⁻¹ -
      (forwardBlowUpSq amplitude second)⁻¹| ≤ _
  rw [inv_sub_inv hf_pos.ne' hs_pos.ne', abs_div]
  calc
    |forwardBlowUpSq amplitude second - forwardBlowUpSq amplitude first| /
          |forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second| ≤
        (slopeEnvelopeForwardRegularity amplitude * dist first second) /
          exactDiamondLowerSq amplitude ^ 2 := hfrac
    _ = slopeEnvelopeInverseRegularity amplitude * dist first second := by
      unfold slopeEnvelopeInverseRegularity
      field_simp [ne_of_gt hlower_sq_pos]

lemma slopeEnvelopeInverseRegularity_nonneg
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude) :
    0 ≤ slopeEnvelopeInverseRegularity amplitude := by
  unfold slopeEnvelopeInverseRegularity
  exact div_nonneg (slopeEnvelopeForwardRegularity_nonneg hadm.1) (sq_nonneg _)

theorem slopeEnvelopeInverseRegularity_lt_previous
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude) :
    slopeEnvelopeInverseRegularity amplitude <
      sharpDiamondInverseRegularity amplitude := by
  have hden : 0 < exactDiamondLowerSq amplitude ^ 2 :=
    sq_pos_of_pos (exactDiamondLowerSq_pos hadm.1
      (admissibleAmplitude_lt_one hadm))
  have hnum := slopeEnvelopeForwardRegularity_lt_coarse hadm.1
  unfold slopeEnvelopeInverseRegularity sharpDiamondInverseRegularity
  rw [div_lt_div_iff₀ hden hden]
  exact mul_lt_mul_of_pos_right hnum hden

theorem slopeEnvelopeInverseMeshTerm_lt_previous
    {amplitude delta : ℝ} (hadm : AdmissibleAmplitude amplitude)
    (hdelta : 0 < delta) :
    slopeEnvelopeInverseMeshTerm amplitude delta <
      sharpDiamondInverseMeshTerm amplitude delta := by
  unfold slopeEnvelopeInverseMeshTerm sharpDiamondInverseMeshTerm
  exact mul_lt_mul_of_pos_right
    (slopeEnvelopeInverseRegularity_lt_previous hadm) hdelta

theorem half_slopeEnvelopeForwardRegularity_exact :
    slopeEnvelopeForwardRegularity (1 / 2 : ℝ) =
      2 + 3 * Real.sqrt (5 / 2 : ℝ) := by
  norm_num [slopeEnvelopeForwardRegularity, exactSlopeRadius]

theorem exists_slopeEnvelope_inverse_finiteCertificate
    {amplitude delta : ℝ}
    (hadm : AdmissibleAmplitude amplitude) (hdelta : 0 < delta) :
    ∃ sample,
      IntrinsicNonradialShearDeltaNet.NoisyUpperSampleValid
          (inverseBlowUpSq amplitude) sample ∧
      IntrinsicNonradialShearDeltaNet.DeltaCoverage
          directionalDiamondBand sample delta ∧
      IntrinsicNonradialShearClosedCore.SampleInside
          directionalDiamondBand sample ∧
      (∀ reading ∈ sample,
        reading.measured = inverseBlowUpSq amplitude reading.point ∧
          reading.error = 0) ∧
      IntrinsicNonradialShearDeltaNet.RegularityCertificate
          directionalDiamondBand sample
          (slopeEnvelopeInverseRegularity amplitude)
          (inverseBlowUpSq amplitude) ∧
      (∀ point ∈ directionalDiamondBand,
        inverseBlowUpSq amplitude point ≤
          IntrinsicNonradialShearDeltaNet.noisySampleUpper sample +
            slopeEnvelopeInverseMeshTerm amplitude delta) ∧
      0 ≤ slopeEnvelopeInverseCertificateGap amplitude delta
        (IntrinsicNonradialShearDeltaNet.noisySampleUpper sample) ∧
      slopeEnvelopeInverseCertificateGap amplitude delta
          (IntrinsicNonradialShearDeltaNet.noisySampleUpper sample) ≤
        slopeEnvelopeInverseMeshTerm amplitude delta := by
  rcases exists_sharp_inverse_diamond_finiteCertificate hadm hdelta with
    ⟨sample, hvalid, hcoverage, hinside, hexact, _,
      _, _, _⟩
  have hregular : IntrinsicNonradialShearDeltaNet.RegularityCertificate
      directionalDiamondBand sample
      (slopeEnvelopeInverseRegularity amplitude)
      (inverseBlowUpSq amplitude) := by
    intro point hpoint reading hreading
    exact slopeEnvelope_inverse_regularity_bound hadm hpoint
      (hinside reading hreading)
  have hglobal : ∀ point ∈ directionalDiamondBand,
      inverseBlowUpSq amplitude point ≤
        IntrinsicNonradialShearDeltaNet.noisySampleUpper sample +
          slopeEnvelopeInverseMeshTerm amplitude delta := by
    intro point hpoint
    simpa [slopeEnvelopeInverseMeshTerm] using
      IntrinsicNonradialShearDeltaNet.global_le_noisySampleUpper_add_regularity
        (slopeEnvelopeInverseRegularity_nonneg hadm)
        hvalid hcoverage hregular point hpoint
  have hupper_pos : 0 ≤ (exactDiamondLowerSq amplitude)⁻¹ :=
    le_of_lt (inv_pos.mpr (exactDiamondLowerSq_pos hadm.1
      (admissibleAmplitude_lt_one hadm)))
  have hsample_upper :
      IntrinsicNonradialShearDeltaNet.noisySampleUpper sample ≤
        (exactDiamondLowerSq amplitude)⁻¹ := by
    apply noisySampleUpper_le_of_exact_bounded hupper_pos hexact
    intro reading hreading
    exact (exactDiamond_inverse_bounds hadm (hinside reading hreading)).2
  have hglobal_at_witness :=
    hglobal (lowerDiamondWitness amplitude) (lowerDiamondWitness_mem hadm.1
      (admissibleAmplitude_lt_one hadm))
  have hwitness := (exactDiamond_inverse_extrema hadm).2
  have hgap_nonneg : 0 ≤ slopeEnvelopeInverseCertificateGap amplitude delta
      (IntrinsicNonradialShearDeltaNet.noisySampleUpper sample) := by
    change inverseBlowUpSq amplitude (lowerDiamondWitness amplitude) ≤ _
      at hglobal_at_witness
    rw [hwitness] at hglobal_at_witness
    simp only [slopeEnvelopeInverseCertificateGap]
    linarith
  have hgap_upper : slopeEnvelopeInverseCertificateGap amplitude delta
        (IntrinsicNonradialShearDeltaNet.noisySampleUpper sample) ≤
      slopeEnvelopeInverseMeshTerm amplitude delta := by
    simp only [slopeEnvelopeInverseCertificateGap]
    linarith
  exact ⟨sample, hvalid, hcoverage, hinside, hexact, hregular, hglobal,
    hgap_nonneg, hgap_upper⟩

end

end BoundaryOfSelf.IntrinsicNonradialShearSlopeEnvelope
