import IntrinsicNonradialShearActualPairTransport

set_option maxHeartbeats 800000

open scoped Topology RealInnerProductSpace
open Set Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearFiniteSaturation

noncomputable section

open StandardHausdorffMetricBridge
open LocalSegmentRealCompletion
open IntrinsicNonradialShearExactSupport
open IntrinsicNonradialShearKernelSharp
open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearRealizableCertificate
open IntrinsicNonradialShearCircleAsymptotic
open IntrinsicNonradialShearChordBridge
open IntrinsicNonradialShearTangentEnvelope
open IntrinsicNonradialShearActualPairTransport

/-! ## IF-BS-22F-F8C26: finite saturation and least global modulus -/

def saturationScale (index : ℕ) : ℝ :=
  diagonalScale (index + 3)

def saturationRadius (index : ℕ) : ℝ :=
  Real.sqrt (1 - saturationScale index ^ 2)

def saturationSigma (X Y : ℝ) (index : ℕ) : ℝ :=
  saturationRadius index * (X + Y) - 2 * saturationScale index

def saturationFirstDirection (X Y : ℝ) (index : ℕ) : AmbientPlane :=
  planeEmbedding
    ({ x := saturationRadius index * X - saturationScale index * Y
       y := saturationRadius index * Y + saturationScale index * X } :
      RealPlanePoint)

def saturationSecondDirection (X Y : ℝ) (index : ℕ) : AmbientPlane :=
  planeEmbedding
    ({ x := saturationRadius index * X + saturationScale index * Y
       y := saturationRadius index * Y - saturationScale index * X } :
      RealPlanePoint)

def saturationFirstPoint (X Y : ℝ) (index : ℕ) : BlowUpPoint :=
  (saturationFirstDirection X Y index,
    saturationSigma X Y index + saturationScale index)

def saturationSecondPoint (X Y : ℝ) (index : ℕ) : BlowUpPoint :=
  (saturationSecondDirection X Y index,
    saturationSigma X Y index - saturationScale index)

def saturationApproximation
    (amplitude X Y : ℝ) (index : ℕ) : ℝ :=
  2 * amplitude *
    (saturationRadius index * Y +
      (X + amplitude) * saturationSigma X Y index)

lemma saturationScale_pos (index : ℕ) :
    0 < saturationScale index :=
  diagonalScale_pos (index + 3)

lemma saturationScale_le_quarter (index : ℕ) :
    saturationScale index ≤ (1 / 4 : ℝ) := by
  rw [saturationScale, diagonalScale]
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  have hindex : 0 ≤ (index : ℝ) := Nat.cast_nonneg index
  have hden : (4 : ℝ) ≤ (index : ℝ) + 4 := by linarith
  have hinv := one_div_le_one_div_of_le
    (a := (4 : ℝ)) (b := (index : ℝ) + 4) (by norm_num) hden
  norm_num only [one_div] at hinv ⊢
  have hsum : (index : ℝ) + 3 + 1 = (index : ℝ) + 4 := by ring
  rw [hsum]
  exact hinv

lemma saturationScale_tendsto_zero :
    Tendsto saturationScale atTop (𝓝 0) := by
  have hshift : Tendsto (fun index : ℕ => index + 3) atTop atTop :=
    tendsto_add_atTop_nat 3
  change Tendsto (fun index : ℕ => diagonalScale (index + 3)) atTop (𝓝 0)
  exact diagonalScale_tendsto_zero.comp hshift

lemma saturationRadicand_nonneg (index : ℕ) :
    0 ≤ 1 - saturationScale index ^ 2 := by
  have hk0 := le_of_lt (saturationScale_pos index)
  have hk4 := saturationScale_le_quarter index
  nlinarith [sq_nonneg (saturationScale index - 1 / 4)]

lemma saturationRadius_nonneg (index : ℕ) :
    0 ≤ saturationRadius index :=
  Real.sqrt_nonneg _

lemma saturationRadius_sq (index : ℕ) :
    saturationRadius index ^ 2 = 1 - saturationScale index ^ 2 := by
  exact Real.sq_sqrt (saturationRadicand_nonneg index)

lemma saturationRadius_ge_three_quarters (index : ℕ) :
    (3 / 4 : ℝ) ≤ saturationRadius index := by
  have hr0 := saturationRadius_nonneg index
  have hk0 := le_of_lt (saturationScale_pos index)
  have hk4 := saturationScale_le_quarter index
  have hrsq := saturationRadius_sq index
  nlinarith [sq_nonneg (saturationScale index - 1 / 4),
    sq_nonneg (saturationRadius index + 3 / 4)]

lemma saturation_rk_unit (index : ℕ) :
    saturationRadius index ^ 2 + saturationScale index ^ 2 = 1 := by
  rw [saturationRadius_sq]
  ring

lemma firstQuadrant_sum_ge_one
    {X Y : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hunit : X ^ 2 + Y ^ 2 = 1) :
    1 ≤ X + Y := by
  have hsum0 : 0 ≤ X + Y := add_nonneg hX0 hY0
  nlinarith [mul_nonneg hX0 hY0, sq_nonneg (X + Y - 1)]

lemma saturationSigma_nonneg
    {X Y : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hunit : X ^ 2 + Y ^ 2 = 1) (index : ℕ) :
    0 ≤ saturationSigma X Y index := by
  have hsum := firstQuadrant_sum_ge_one hX0 hY0 hunit
  have hr := saturationRadius_ge_three_quarters index
  have hk := saturationScale_le_quarter index
  have hr0 := saturationRadius_nonneg index
  have hprod : (3 / 4 : ℝ) ≤ saturationRadius index * (X + Y) := by
    calc
      (3 / 4 : ℝ) = (3 / 4) * 1 := by ring
      _ ≤ saturationRadius index * (X + Y) :=
        mul_le_mul hr hsum (by norm_num) hr0
  unfold saturationSigma
  linarith

lemma saturationSecondSlope_nonneg
    {X Y : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hunit : X ^ 2 + Y ^ 2 = 1) (index : ℕ) :
    0 ≤ saturationSigma X Y index - saturationScale index := by
  have hsum := firstQuadrant_sum_ge_one hX0 hY0 hunit
  have hr := saturationRadius_ge_three_quarters index
  have hk := saturationScale_le_quarter index
  have hr0 := saturationRadius_nonneg index
  have hprod : (3 / 4 : ℝ) ≤ saturationRadius index * (X + Y) := by
    calc
      (3 / 4 : ℝ) = (3 / 4) * 1 := by ring
      _ ≤ saturationRadius index * (X + Y) :=
        mul_le_mul hr hsum (by norm_num) hr0
  unfold saturationSigma
  linarith

lemma saturationFirst_unit
    {X Y : ℝ} (hunit : X ^ 2 + Y ^ 2 = 1) (index : ℕ) :
    (saturationFirstDirection X Y index).ofLp 0 ^ 2 +
      (saturationFirstDirection X Y index).ofLp 1 ^ 2 = 1 := by
  have hrk := saturation_rk_unit index
  simp [saturationFirstDirection, planeEmbedding]
  nlinarith [sq_nonneg
    (saturationRadius index * X - saturationScale index * Y),
    sq_nonneg
    (saturationRadius index * Y + saturationScale index * X)]

lemma saturationSecond_unit
    {X Y : ℝ} (hunit : X ^ 2 + Y ^ 2 = 1) (index : ℕ) :
    (saturationSecondDirection X Y index).ofLp 0 ^ 2 +
      (saturationSecondDirection X Y index).ofLp 1 ^ 2 = 1 := by
  have hrk := saturation_rk_unit index
  simp [saturationSecondDirection, planeEmbedding]
  nlinarith [sq_nonneg
    (saturationRadius index * X + saturationScale index * Y),
    sq_nonneg
    (saturationRadius index * Y - saturationScale index * X)]

lemma direction_mem_sphere_of_unit
    {direction : AmbientPlane}
    (hunit : direction.ofLp 0 ^ 2 + direction.ofLp 1 ^ 2 = 1) :
    direction ∈ Metric.sphere kernelOrigin 1 := by
  rw [Metric.mem_sphere, dist_comm]
  have hdist := dist_sq_eq_coordinate_sq_sum kernelOrigin direction
  have hx0 : kernelOrigin.ofLp 0 = 0 := by simp [kernelOrigin, planeEmbedding]
  have hy0 : kernelOrigin.ofLp 1 = 0 := by simp [kernelOrigin, planeEmbedding]
  rw [hx0, hy0] at hdist
  simp only [zero_sub, neg_sq] at hdist
  have hsq : dist kernelOrigin direction ^ 2 = 1 := by nlinarith
  nlinarith [(dist_nonneg : 0 ≤ dist kernelOrigin direction)]

lemma saturationFirstPoint_mem
    {X Y : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hunit : X ^ 2 + Y ^ 2 = 1) (index : ℕ) :
    saturationFirstPoint X Y index ∈ directionalDiamondBand := by
  have hY1 :=
    (IntrinsicNonradialShearCenteredEnvelope.unit_quadrant_coordinate_le_one
      hX0 hY0 hunit).2
  have hk0 := le_of_lt (saturationScale_pos index)
  have hslope0 : 0 ≤ (saturationFirstPoint X Y index).2 := by
    simp only [saturationFirstPoint]
    exact add_nonneg (saturationSigma_nonneg hX0 hY0 hunit index) hk0
  have hsigned : (saturationFirstPoint X Y index).2 ≤
      (saturationFirstPoint X Y index).1.ofLp 0 +
        (saturationFirstPoint X Y index).1.ofLp 1 := by
    simp [saturationFirstPoint, saturationFirstDirection, saturationSigma,
      planeEmbedding]
    have : -1 ≤ X - Y := by nlinarith
    nlinarith [mul_nonneg hk0 (by linarith : 0 ≤ 1 + X - Y)]
  have hwidth : (saturationFirstPoint X Y index).2 ≤
      |(saturationFirstPoint X Y index).1.ofLp 0| +
        |(saturationFirstPoint X Y index).1.ofLp 1| :=
    hsigned.trans (add_le_add (le_abs_self _) (le_abs_self _))
  have habs : |(saturationFirstPoint X Y index).2| ≤
      |(saturationFirstPoint X Y index).1.ofLp 0| +
        |(saturationFirstPoint X Y index).1.ofLp 1| := by
    rw [abs_of_nonneg hslope0]
    exact hwidth
  have hunit' := saturationFirst_unit hunit index
  have hsqrt := unit_width_le_sqrt_two hunit'
  rw [directionalDiamondBand]
  exact ⟨⟨direction_mem_sphere_of_unit hunit', abs_le.mp (habs.trans hsqrt)⟩,
    habs⟩

lemma saturationSecondPoint_mem
    {X Y : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hunit : X ^ 2 + Y ^ 2 = 1) (index : ℕ) :
    saturationSecondPoint X Y index ∈ directionalDiamondBand := by
  have hX1 :=
    (IntrinsicNonradialShearCenteredEnvelope.unit_quadrant_coordinate_le_one
      hX0 hY0 hunit).1
  have hslope0 : 0 ≤ (saturationSecondPoint X Y index).2 := by
    simpa [saturationSecondPoint] using
      saturationSecondSlope_nonneg hX0 hY0 hunit index
  have hk0 := le_of_lt (saturationScale_pos index)
  have hsigned : (saturationSecondPoint X Y index).2 ≤
      (saturationSecondPoint X Y index).1.ofLp 0 +
        (saturationSecondPoint X Y index).1.ofLp 1 := by
    simp [saturationSecondPoint, saturationSecondDirection, saturationSigma,
      planeEmbedding]
    have : X - Y ≤ 1 := by nlinarith
    nlinarith [mul_nonneg hk0 (by linarith : 0 ≤ 3 - X + Y)]
  have hwidth : (saturationSecondPoint X Y index).2 ≤
      |(saturationSecondPoint X Y index).1.ofLp 0| +
        |(saturationSecondPoint X Y index).1.ofLp 1| :=
    hsigned.trans (add_le_add (le_abs_self _) (le_abs_self _))
  have habs : |(saturationSecondPoint X Y index).2| ≤
      |(saturationSecondPoint X Y index).1.ofLp 0| +
        |(saturationSecondPoint X Y index).1.ofLp 1| := by
    rw [abs_of_nonneg hslope0]
    exact hwidth
  have hunit' := saturationSecond_unit hunit index
  have hsqrt := unit_width_le_sqrt_two hunit'
  rw [directionalDiamondBand]
  exact ⟨⟨direction_mem_sphere_of_unit hunit', abs_le.mp (habs.trans hsqrt)⟩,
    habs⟩

lemma saturation_direction_dist
    {X Y : ℝ} (hunit : X ^ 2 + Y ^ 2 = 1) (index : ℕ) :
    dist (saturationFirstDirection X Y index)
        (saturationSecondDirection X Y index) =
      2 * saturationScale index := by
  have hsq := dist_sq_eq_coordinate_sq_sum
    (saturationFirstDirection X Y index)
    (saturationSecondDirection X Y index)
  have htargetSq :
      dist (saturationFirstDirection X Y index)
          (saturationSecondDirection X Y index) ^ 2 =
        (2 * saturationScale index) ^ 2 := by
    rw [hsq]
    simp [saturationFirstDirection, saturationSecondDirection, planeEmbedding]
    nlinarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg).1 htargetSq with heq | heq
  · exact heq
  · have hleft0 : 0 ≤ dist (saturationFirstDirection X Y index)
        (saturationSecondDirection X Y index) := dist_nonneg
    have hright0 : 0 ≤ 2 * saturationScale index :=
      mul_nonneg (by norm_num) (le_of_lt (saturationScale_pos index))
    nlinarith

theorem saturation_pair_dist
    {X Y : ℝ} (hunit : X ^ 2 + Y ^ 2 = 1) (index : ℕ) :
    dist (saturationFirstPoint X Y index)
        (saturationSecondPoint X Y index) =
      2 * saturationScale index := by
  rw [Prod.dist_eq]
  have hdir := saturation_direction_dist hunit index
  have hslope :
      dist (saturationSigma X Y index + saturationScale index)
        (saturationSigma X Y index - saturationScale index) =
      2 * saturationScale index := by
    rw [Real.dist_eq]
    rw [show saturationSigma X Y index + saturationScale index -
        (saturationSigma X Y index - saturationScale index) =
          2 * saturationScale index by ring]
    rw [abs_of_nonneg]
    exact mul_nonneg (by norm_num) (le_of_lt (saturationScale_pos index))
  change max
      (dist (saturationFirstDirection X Y index)
        (saturationSecondDirection X Y index))
      (dist (saturationSigma X Y index + saturationScale index)
        (saturationSigma X Y index - saturationScale index)) =
    2 * saturationScale index
  rw [hdir, hslope, max_self]

theorem saturation_forward_difference
    {amplitude X Y : ℝ} (ha0 : 0 ≤ amplitude)
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hunit : X ^ 2 + Y ^ 2 = 1) (index : ℕ) :
    |forwardBlowUpSq amplitude (saturationFirstPoint X Y index) -
        forwardBlowUpSq amplitude (saturationSecondPoint X Y index)| =
      saturationApproximation amplitude X Y index *
        (2 * saturationScale index) := by
  have hfirst := saturationFirstPoint_mem hX0 hY0 hunit index
  have hsecond := saturationSecondPoint_mem hX0 hY0 hunit index
  have hσ0 := saturationSigma_nonneg hX0 hY0 hunit index
  have hbracket0 : 0 ≤ saturationRadius index * Y +
      (X + amplitude) * saturationSigma X Y index :=
    add_nonneg
      (mul_nonneg (saturationRadius_nonneg index) hY0)
      (mul_nonneg (add_nonneg hX0 ha0) hσ0)
  have hraw :
      forwardBlowUpSq amplitude (saturationFirstPoint X Y index) -
          forwardBlowUpSq amplitude (saturationSecondPoint X Y index) =
        4 * amplitude * saturationScale index *
          (saturationRadius index * Y +
            (X + amplitude) * saturationSigma X Y index) := by
    rw [forwardBlowUpSq_eq_unit_excess hfirst,
      forwardBlowUpSq_eq_unit_excess hsecond]
    simp [saturationFirstPoint, saturationSecondPoint,
      saturationFirstDirection, saturationSecondDirection, planeEmbedding]
    ring
  have hraw0 : 0 ≤ 4 * amplitude * saturationScale index *
      (saturationRadius index * Y +
        (X + amplitude) * saturationSigma X Y index) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) ha0)
        (le_of_lt (saturationScale_pos index))) hbracket0
  rw [hraw, abs_of_nonneg hraw0]
  unfold saturationApproximation
  ring

lemma saturationRadius_tendsto_one :
    Tendsto saturationRadius atTop (𝓝 1) := by
  have hradicand : Tendsto
      (fun index => 1 - saturationScale index ^ 2) atTop (𝓝 (1 : ℝ)) := by
    convert tendsto_const_nhds.sub (saturationScale_tendsto_zero.pow 2) using 1 <;>
      norm_num
  have hsqrt : ContinuousAt (fun value : ℝ => Real.sqrt value) 1 :=
    continuousAt_id.sqrt
  change Tendsto (fun index : ℕ =>
    Real.sqrt (1 - saturationScale index ^ 2)) atTop (𝓝 1)
  convert hsqrt.tendsto.comp hradicand using 1 <;>
    simp [Function.comp_def]

lemma saturationSigma_tendsto_sum (X Y : ℝ) :
    Tendsto (saturationSigma X Y) atTop (𝓝 (X + Y)) := by
  unfold saturationSigma
  convert (saturationRadius_tendsto_one.mul_const (X + Y)).sub
      (saturationScale_tendsto_zero.const_mul 2) using 1 <;>
    ring

theorem saturationApproximation_tendsto
    (amplitude X Y : ℝ) :
    Tendsto (saturationApproximation amplitude X Y) atTop
      (𝓝 (2 * amplitude * (Y + (X + amplitude) * (X + Y)))) := by
  unfold saturationApproximation
  convert tendsto_const_nhds.mul
    ((saturationRadius_tendsto_one.mul_const Y).add
      (tendsto_const_nhds.mul (saturationSigma_tendsto_sum X Y))) using 1 <;>
    ring

def GlobalDiamondChordModuli (amplitude : ℝ) : Set ℝ :=
  {constant | ∀ first ∈ directionalDiamondBand,
    ∀ second ∈ directionalDiamondBand,
      |forwardBlowUpSq amplitude first - forwardBlowUpSq amplitude second| ≤
        constant * dist first second}

theorem exactLocalTangentModulus_mem_global
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    exactLocalTangentModulus amplitude ∈ GlobalDiamondChordModuli amplitude := by
  intro first hfirst second hsecond
  exact forwardBlowUpSq_actual_pair_exact_bound ha0 hfirst hsecond

/-- The F8C25 roof is sharp: finite admissible pairs converge to the exact
tangent witness, hence no smaller global chord modulus exists. -/
theorem exactLocalTangentModulus_isLeast_global
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    IsLeast (GlobalDiamondChordModuli amplitude)
      (exactLocalTangentModulus amplitude) := by
  refine ⟨exactLocalTangentModulus_mem_global ha0, ?_⟩
  intro constant hconstant
  let X : ℝ := (tangentEnvelopePoint amplitude).1
  let Y : ℝ := (tangentEnvelopePoint amplitude).2
  have hpoint := tangentEnvelopePoint_mem amplitude
  have hX0 : 0 ≤ X := hpoint.1.1.1
  have hY0 : 0 ≤ Y := hpoint.1.2.1
  have hunit : X ^ 2 + Y ^ 2 = 1 := hpoint.2
  have hbound : ∀ index,
      saturationApproximation amplitude X Y index ≤ constant := by
    intro index
    have hfirst := saturationFirstPoint_mem hX0 hY0 hunit index
    have hsecond := saturationSecondPoint_mem hX0 hY0 hunit index
    have hglobal := hconstant
      (saturationFirstPoint X Y index) hfirst
      (saturationSecondPoint X Y index) hsecond
    rw [saturation_forward_difference ha0 hX0 hY0 hunit index,
      saturation_pair_dist hunit index] at hglobal
    have hscale : 0 < 2 * saturationScale index :=
      mul_pos (by norm_num) (saturationScale_pos index)
    exact le_of_mul_le_mul_right hglobal hscale
  have hlimit := le_of_tendsto'
    (saturationApproximation_tendsto amplitude X Y) hbound
  have henvelope :
      exactTangentEnvelope amplitude = Y + (X + amplitude) * (X + Y) := by
    rw [exactTangentEnvelope, scalarTangentDensity]
    dsimp [X, Y]
    ring
  unfold exactLocalTangentModulus
  rw [henvelope]
  exact hlimit

end

end BoundaryOfSelf.IntrinsicNonradialShearFiniteSaturation
