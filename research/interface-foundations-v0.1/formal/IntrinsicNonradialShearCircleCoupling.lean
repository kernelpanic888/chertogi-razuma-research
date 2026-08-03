import IntrinsicNonradialShearSlopeEnvelope

open scoped Topology RealInnerProductSpace
open Set Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearCircleCoupling

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
open IntrinsicNonradialShearSlopeEnvelope

/-! ## IF-BS-22F-F8C19: circle coupling and strict non-attainment -/

def circlePairSumSq (first second : AmbientPlane) : ℝ :=
  (first.ofLp 0 + second.ofLp 0) ^ 2 +
    (first.ofLp 1 + second.ofLp 1) ^ 2

lemma circle_xSquare_coupled_bounds
    {first second : AmbientPlane}
    (hfirst : first ∈ Metric.sphere kernelOrigin 1)
    (hsecond : second ∈ Metric.sphere kernelOrigin 1) :
    4 * (first.ofLp 0 ^ 2 - second.ofLp 0 ^ 2) ^ 2 ≤
        circlePairSumSq first second * dist first second ^ 2 ∧
      circlePairSumSq first second + dist first second ^ 2 = 4 := by
  let x₁ : ℝ := first.ofLp 0
  let y₁ : ℝ := first.ofLp 1
  let x₂ : ℝ := second.ofLp 0
  let y₂ : ℝ := second.ofLp 1
  let p : ℝ := x₁ + x₂
  let q : ℝ := x₁ - x₂
  let r : ℝ := y₁ + y₂
  let s : ℝ := y₁ - y₂
  rw [Metric.mem_sphere] at hfirst hsecond
  rw [dist_comm] at hfirst hsecond
  have hunit₁ := dist_sq_eq_coordinate_sq_sum kernelOrigin first
  have hunit₂ := dist_sq_eq_coordinate_sq_sum kernelOrigin second
  rw [hfirst] at hunit₁
  rw [hsecond] at hunit₂
  simp [kernelOrigin, planeEmbedding] at hunit₁ hunit₂
  have hdist := dist_sq_eq_coordinate_sq_sum first second
  have horth : p * q + r * s = 0 := by
    dsimp [p, q, r, s, x₁, x₂, y₁, y₂]
    nlinarith
  have horthSq : (p * q + r * s) ^ 2 = 0 := by rw [horth]; norm_num
  have hcoupled :
      4 * (p * q) ^ 2 ≤ (p ^ 2 + r ^ 2) * (q ^ 2 + s ^ 2) := by
    nlinarith [sq_nonneg (p * s + r * q)]
  have hdelta :
      first.ofLp 0 ^ 2 - second.ofLp 0 ^ 2 = p * q := by
    dsimp [p, q, x₁, x₂]
    ring
  have hsum :
      circlePairSumSq first second = p ^ 2 + r ^ 2 := by
    simp [circlePairSumSq, p, r, x₁, x₂, y₁, y₂]
  have hdistSq : dist first second ^ 2 = q ^ 2 + s ^ 2 := by
    simpa [q, s, x₁, x₂, y₁, y₂] using hdist
  constructor
  · rw [hdelta, hsum, hdistSq]
    exact hcoupled
  · rw [hsum, hdistSq]
    dsimp [p, q, r, s, x₁, x₂, y₁, y₂]
    nlinarith

theorem circle_xSquare_bound
    {first second : AmbientPlane}
    (hfirst : first ∈ Metric.sphere kernelOrigin 1)
    (hsecond : second ∈ Metric.sphere kernelOrigin 1) :
    |first.ofLp 0 ^ 2 - second.ofLp 0 ^ 2| ≤ dist first second := by
  rcases circle_xSquare_coupled_bounds hfirst hsecond with ⟨hcoupled, hsum⟩
  have hpair_le : circlePairSumSq first second ≤ 4 := by
    nlinarith [sq_nonneg (dist first second)]
  have hdistSq0 : 0 ≤ dist first second ^ 2 := sq_nonneg _
  have hproduct :
      circlePairSumSq first second * dist first second ^ 2 ≤
        4 * dist first second ^ 2 :=
    mul_le_mul_of_nonneg_right hpair_le hdistSq0
  have hsquare :
      (first.ofLp 0 ^ 2 - second.ofLp 0 ^ 2) ^ 2 ≤
        dist first second ^ 2 := by
    nlinarith
  nlinarith [sq_abs (first.ofLp 0 ^ 2 - second.ofLp 0 ^ 2),
    abs_nonneg (first.ofLp 0 ^ 2 - second.ofLp 0 ^ 2),
    (dist_nonneg : 0 ≤ dist first second)]

theorem circle_xSquare_strict
    {first second : AmbientPlane}
    (hfirst : first ∈ Metric.sphere kernelOrigin 1)
    (hsecond : second ∈ Metric.sphere kernelOrigin 1)
    (hne : first ≠ second) :
    |first.ofLp 0 ^ 2 - second.ofLp 0 ^ 2| < dist first second := by
  have hDpos : 0 < dist first second := dist_pos.mpr hne
  have hDsqpos : 0 < dist first second ^ 2 := sq_pos_of_pos hDpos
  rcases circle_xSquare_coupled_bounds hfirst hsecond with ⟨hcoupled, hsum⟩
  by_contra hnot
  have hreverse :
      dist first second ≤
        |first.ofLp 0 ^ 2 - second.ofLp 0 ^ 2| := le_of_not_gt hnot
  have hreverseSq :
      dist first second ^ 2 ≤
        (first.ofLp 0 ^ 2 - second.ofLp 0 ^ 2) ^ 2 := by
    nlinarith [sq_abs (first.ofLp 0 ^ 2 - second.ofLp 0 ^ 2),
      abs_nonneg (first.ofLp 0 ^ 2 - second.ofLp 0 ^ 2)]
  have hfour :
      4 * dist first second ^ 2 ≤
        circlePairSumSq first second * dist first second ^ 2 := by
    nlinarith
  have hpair_lt : circlePairSumSq first second < 4 := by nlinarith
  have hproduct_lt :
      circlePairSumSq first second * dist first second ^ 2 <
        4 * dist first second ^ 2 :=
    mul_lt_mul_of_pos_right hpair_lt hDsqpos
  linarith

theorem diamond_xSquare_bound
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand) :
    |first.1.ofLp 0 ^ 2 - second.1.ofLp 0 ^ 2| ≤ dist first second := by
  exact (circle_xSquare_bound
      (diamond_mem_relaxedChamber hfirst).1
      (diamond_mem_relaxedChamber hsecond).1).trans
    (blowUp_direction_dist_le first second)

theorem diamond_xSquare_strict
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand)
    (hne : first ≠ second) :
    |first.1.ofLp 0 ^ 2 - second.1.ofLp 0 ^ 2| < dist first second := by
  by_cases hdirection : first.1 = second.1
  · have hDpos : 0 < dist first second := dist_pos.mpr hne
    rw [hdirection]
    simpa only [sub_self, abs_zero] using hDpos
  · exact (circle_xSquare_strict
      (diamond_mem_relaxedChamber hfirst).1
      (diamond_mem_relaxedChamber hsecond).1 hdirection).trans_le
        (blowUp_direction_dist_le first second)

lemma slopeSquareDifference_bound
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude)
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand) :
    |(first.1.ofLp 1 + amplitude * first.2) ^ 2 -
        (second.1.ofLp 1 + amplitude * second.2) ^ 2| ≤
      2 * (1 + amplitude) * exactSlopeRadius amplitude *
        dist first second := by
  let v₁ : ℝ := first.1.ofLp 1 + amplitude * first.2
  let v₂ : ℝ := second.1.ofLp 1 + amplitude * second.2
  let D : ℝ := dist first second
  let R : ℝ := exactSlopeRadius amplitude
  have hD0 : 0 ≤ D := dist_nonneg
  have hR0 : 0 ≤ R := le_of_lt (exactSlopeRadius_pos ha0)
  have hv₁ : |v₁| ≤ R := exactSlopeRadius_bound ha0 hfirst
  have hv₂ : |v₂| ≤ R := exactSlopeRadius_bound ha0 hsecond
  have hyDifference :
      |first.1.ofLp 1 - second.1.ofLp 1| ≤ D :=
    blowUp_y_sub_abs_le_dist first second
  have hsDifference : |first.2 - second.2| ≤ D :=
    blowUp_slope_sub_abs_le_dist first second
  have hvDifference : |v₁ - v₂| ≤ (1 + amplitude) * D := by
    calc
      |v₁ - v₂| =
          |(first.1.ofLp 1 - second.1.ofLp 1) +
            amplitude * (first.2 - second.2)| := by
              congr 1
              dsimp [v₁, v₂]
              ring
      _ ≤ |first.1.ofLp 1 - second.1.ofLp 1| +
          |amplitude * (first.2 - second.2)| := abs_add_le _ _
      _ = |first.1.ofLp 1 - second.1.ofLp 1| +
          amplitude * |first.2 - second.2| := by
            rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ D + amplitude * D := by
        exact add_le_add hyDifference
          (mul_le_mul_of_nonneg_left hsDifference ha0)
      _ = (1 + amplitude) * D := by ring
  have hvSum : |v₁ + v₂| ≤ 2 * R := by
    calc
      |v₁ + v₂| ≤ |v₁| + |v₂| := abs_add_le _ _
      _ ≤ 2 * R := by linarith
  have hvRight0 : 0 ≤ (1 + amplitude) * D :=
    mul_nonneg (by linarith) hD0
  rw [show v₁ ^ 2 - v₂ ^ 2 = (v₁ - v₂) * (v₁ + v₂) by ring]
  rw [abs_mul]
  have hmul := mul_le_mul hvDifference hvSum (abs_nonneg _) hvRight0
  dsimp [v₁, v₂, D, R] at *
  nlinarith

def circleCoupledForwardRegularity (amplitude : ℝ) : ℝ :=
  1 + 2 * (1 + amplitude) * exactSlopeRadius amplitude

lemma circleCoupledForwardRegularity_nonneg
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    0 ≤ circleCoupledForwardRegularity amplitude := by
  unfold circleCoupledForwardRegularity
  have hr0 : 0 ≤ exactSlopeRadius amplitude :=
    le_of_lt (exactSlopeRadius_pos ha0)
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + amplitude) hr0]

theorem circleCoupled_forward_regularity_bound
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude)
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand) :
    |forwardBlowUpSq amplitude first -
        forwardBlowUpSq amplitude second| ≤
      circleCoupledForwardRegularity amplitude * dist first second := by
  have hx := diamond_xSquare_bound hfirst hsecond
  have hv := slopeSquareDifference_bound ha0 hfirst hsecond
  calc
    |forwardBlowUpSq amplitude first -
        forwardBlowUpSq amplitude second| ≤
      |first.1.ofLp 0 ^ 2 - second.1.ofLp 0 ^ 2| +
        |(first.1.ofLp 1 + amplitude * first.2) ^ 2 -
          (second.1.ofLp 1 + amplitude * second.2) ^ 2| := by
            rw [show forwardBlowUpSq amplitude first -
                forwardBlowUpSq amplitude second =
              (first.1.ofLp 0 ^ 2 - second.1.ofLp 0 ^ 2) +
                ((first.1.ofLp 1 + amplitude * first.2) ^ 2 -
                  (second.1.ofLp 1 + amplitude * second.2) ^ 2) by
                    simp [forwardBlowUpSq]; ring]
            exact abs_add_le _ _
    _ ≤ dist first second +
        2 * (1 + amplitude) * exactSlopeRadius amplitude *
          dist first second := add_le_add hx hv
    _ = circleCoupledForwardRegularity amplitude * dist first second := by
      unfold circleCoupledForwardRegularity
      ring

theorem circleCoupled_forward_regularity_strict
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude)
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand)
    (hne : first ≠ second) :
    |forwardBlowUpSq amplitude first -
        forwardBlowUpSq amplitude second| <
      circleCoupledForwardRegularity amplitude * dist first second := by
  have hx := diamond_xSquare_strict hfirst hsecond hne
  have hv := slopeSquareDifference_bound ha0 hfirst hsecond
  calc
    |forwardBlowUpSq amplitude first -
        forwardBlowUpSq amplitude second| ≤
      |first.1.ofLp 0 ^ 2 - second.1.ofLp 0 ^ 2| +
        |(first.1.ofLp 1 + amplitude * first.2) ^ 2 -
          (second.1.ofLp 1 + amplitude * second.2) ^ 2| := by
            rw [show forwardBlowUpSq amplitude first -
                forwardBlowUpSq amplitude second =
              (first.1.ofLp 0 ^ 2 - second.1.ofLp 0 ^ 2) +
                ((first.1.ofLp 1 + amplitude * first.2) ^ 2 -
                  (second.1.ofLp 1 + amplitude * second.2) ^ 2) by
                    simp [forwardBlowUpSq]; ring]
            exact abs_add_le _ _
    _ < dist first second +
        2 * (1 + amplitude) * exactSlopeRadius amplitude *
          dist first second := add_lt_add_of_lt_of_le hx hv
    _ = circleCoupledForwardRegularity amplitude * dist first second := by
      unfold circleCoupledForwardRegularity
      ring

theorem circleCoupledForwardRegularity_lt_slopeEnvelope
    (amplitude : ℝ) :
    circleCoupledForwardRegularity amplitude <
      slopeEnvelopeForwardRegularity amplitude := by
  unfold circleCoupledForwardRegularity slopeEnvelopeForwardRegularity
  linarith

def circleCoupledInverseRegularity (amplitude : ℝ) : ℝ :=
  circleCoupledForwardRegularity amplitude /
    (exactDiamondLowerSq amplitude) ^ 2

def circleCoupledInverseMeshTerm (amplitude delta : ℝ) : ℝ :=
  circleCoupledInverseRegularity amplitude * delta

def circleCoupledInverseCertificateGap
    (amplitude delta sampleMax : ℝ) : ℝ :=
  sampleMax + circleCoupledInverseMeshTerm amplitude delta -
    (exactDiamondLowerSq amplitude)⁻¹

theorem circleCoupled_inverse_regularity_bound
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude)
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand) :
    |inverseBlowUpSq amplitude first - inverseBlowUpSq amplitude second| ≤
      circleCoupledInverseRegularity amplitude * dist first second := by
  have hreg := circleCoupled_forward_regularity_bound hadm.1 hfirst hsecond
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
  have hlower_sq_pos : 0 < exactDiamondLowerSq amplitude ^ 2 :=
    sq_pos_of_pos hlower_pos
  have hnum : |forwardBlowUpSq amplitude second -
      forwardBlowUpSq amplitude first| ≤
        circleCoupledForwardRegularity amplitude * dist first second := by
    simpa [abs_sub_comm] using hreg
  have htarget_nonneg : 0 ≤
      circleCoupledForwardRegularity amplitude * dist first second :=
    mul_nonneg (circleCoupledForwardRegularity_nonneg hadm.1) dist_nonneg
  have hfrac : |forwardBlowUpSq amplitude second -
        forwardBlowUpSq amplitude first| /
      |forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second| ≤
        (circleCoupledForwardRegularity amplitude * dist first second) /
          exactDiamondLowerSq amplitude ^ 2 :=
    div_le_div₀ htarget_nonneg hnum hlower_sq_pos hden
  change |(forwardBlowUpSq amplitude first)⁻¹ -
      (forwardBlowUpSq amplitude second)⁻¹| ≤ _
  rw [inv_sub_inv hf_pos.ne' hs_pos.ne', abs_div]
  calc
    |forwardBlowUpSq amplitude second - forwardBlowUpSq amplitude first| /
          |forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second| ≤
        (circleCoupledForwardRegularity amplitude * dist first second) /
          exactDiamondLowerSq amplitude ^ 2 := hfrac
    _ = circleCoupledInverseRegularity amplitude * dist first second := by
      unfold circleCoupledInverseRegularity
      field_simp [ne_of_gt hlower_sq_pos]

lemma circleCoupledInverseRegularity_nonneg
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude) :
    0 ≤ circleCoupledInverseRegularity amplitude := by
  unfold circleCoupledInverseRegularity
  exact div_nonneg (circleCoupledForwardRegularity_nonneg hadm.1) (sq_nonneg _)

theorem circleCoupledInverseRegularity_lt_slopeEnvelope
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude) :
    circleCoupledInverseRegularity amplitude <
      slopeEnvelopeInverseRegularity amplitude := by
  have hden : 0 < exactDiamondLowerSq amplitude ^ 2 :=
    sq_pos_of_pos (exactDiamondLowerSq_pos hadm.1
      (admissibleAmplitude_lt_one hadm))
  have hnum := circleCoupledForwardRegularity_lt_slopeEnvelope amplitude
  unfold circleCoupledInverseRegularity slopeEnvelopeInverseRegularity
  rw [div_lt_div_iff₀ hden hden]
  exact mul_lt_mul_of_pos_right hnum hden

theorem circleCoupledInverseMeshTerm_lt_slopeEnvelope
    {amplitude delta : ℝ} (hadm : AdmissibleAmplitude amplitude)
    (hdelta : 0 < delta) :
    circleCoupledInverseMeshTerm amplitude delta <
      slopeEnvelopeInverseMeshTerm amplitude delta := by
  unfold circleCoupledInverseMeshTerm slopeEnvelopeInverseMeshTerm
  exact mul_lt_mul_of_pos_right
    (circleCoupledInverseRegularity_lt_slopeEnvelope hadm) hdelta

theorem half_circleCoupledForwardRegularity_exact :
    circleCoupledForwardRegularity (1 / 2 : ℝ) =
      1 + 3 * Real.sqrt (5 / 2 : ℝ) := by
  norm_num [circleCoupledForwardRegularity, exactSlopeRadius]

theorem exists_circleCoupled_inverse_finiteCertificate
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
          (circleCoupledInverseRegularity amplitude)
          (inverseBlowUpSq amplitude) ∧
      (∀ point ∈ directionalDiamondBand,
        inverseBlowUpSq amplitude point ≤
          IntrinsicNonradialShearDeltaNet.noisySampleUpper sample +
            circleCoupledInverseMeshTerm amplitude delta) ∧
      0 ≤ circleCoupledInverseCertificateGap amplitude delta
        (IntrinsicNonradialShearDeltaNet.noisySampleUpper sample) ∧
      circleCoupledInverseCertificateGap amplitude delta
          (IntrinsicNonradialShearDeltaNet.noisySampleUpper sample) ≤
        circleCoupledInverseMeshTerm amplitude delta := by
  rcases exists_slopeEnvelope_inverse_finiteCertificate hadm hdelta with
    ⟨sample, hvalid, hcoverage, hinside, hexact, _, _, _, _⟩
  have hregular : IntrinsicNonradialShearDeltaNet.RegularityCertificate
      directionalDiamondBand sample
      (circleCoupledInverseRegularity amplitude)
      (inverseBlowUpSq amplitude) := by
    intro point hpoint reading hreading
    exact circleCoupled_inverse_regularity_bound hadm hpoint
      (hinside reading hreading)
  have hglobal : ∀ point ∈ directionalDiamondBand,
      inverseBlowUpSq amplitude point ≤
        IntrinsicNonradialShearDeltaNet.noisySampleUpper sample +
          circleCoupledInverseMeshTerm amplitude delta := by
    intro point hpoint
    simpa [circleCoupledInverseMeshTerm] using
      IntrinsicNonradialShearDeltaNet.global_le_noisySampleUpper_add_regularity
        (circleCoupledInverseRegularity_nonneg hadm)
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
  have hgap_nonneg : 0 ≤ circleCoupledInverseCertificateGap amplitude delta
      (IntrinsicNonradialShearDeltaNet.noisySampleUpper sample) := by
    change inverseBlowUpSq amplitude (lowerDiamondWitness amplitude) ≤ _
      at hglobal_at_witness
    rw [hwitness] at hglobal_at_witness
    simp only [circleCoupledInverseCertificateGap]
    linarith
  have hgap_upper : circleCoupledInverseCertificateGap amplitude delta
        (IntrinsicNonradialShearDeltaNet.noisySampleUpper sample) ≤
      circleCoupledInverseMeshTerm amplitude delta := by
    simp only [circleCoupledInverseCertificateGap]
    linarith
  exact ⟨sample, hvalid, hcoverage, hinside, hexact, hregular, hglobal,
    hgap_nonneg, hgap_upper⟩

end

end BoundaryOfSelf.IntrinsicNonradialShearCircleCoupling
