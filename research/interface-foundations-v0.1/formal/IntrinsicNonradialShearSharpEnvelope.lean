import IntrinsicNonradialShearRealizableCertificate

open scoped Topology RealInnerProductSpace
open Set Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearSharpEnvelope

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

/-! ## IF-BS-22F-F8C17: sharp spectral envelope on the exact diamond -/

def lowerRadicand (amplitude : ℝ) : ℝ :=
  (1 - amplitude) ^ 2 + 1

def upperRadicand (amplitude : ℝ) : ℝ :=
  (1 + amplitude) ^ 2 + 1

def exactDiamondLowerSq (amplitude : ℝ) : ℝ :=
  1 - amplitude + amplitude ^ 2 -
    amplitude * Real.sqrt (lowerRadicand amplitude)

def exactDiamondUpperSq (amplitude : ℝ) : ℝ :=
  1 + amplitude + amplitude ^ 2 +
    amplitude * Real.sqrt (upperRadicand amplitude)

lemma lowerRadicand_pos (amplitude : ℝ) :
    0 < lowerRadicand amplitude := by
  unfold lowerRadicand
  positivity

lemma upperRadicand_pos (amplitude : ℝ) :
    0 < upperRadicand amplitude := by
  unfold upperRadicand
  positivity

lemma lowerRoot_sq (amplitude : ℝ) :
    Real.sqrt (lowerRadicand amplitude) ^ 2 =
      lowerRadicand amplitude := by
  exact Real.sq_sqrt (le_of_lt (lowerRadicand_pos amplitude))

lemma upperRoot_sq (amplitude : ℝ) :
    Real.sqrt (upperRadicand amplitude) ^ 2 =
      upperRadicand amplitude := by
  exact Real.sq_sqrt (le_of_lt (upperRadicand_pos amplitude))

lemma lowerRoot_ge_one (amplitude : ℝ) :
    1 ≤ Real.sqrt (lowerRadicand amplitude) := by
  have hr0 := Real.sqrt_nonneg (lowerRadicand amplitude)
  have hrsq := lowerRoot_sq amplitude
  by_contra h
  have hr1 : Real.sqrt (lowerRadicand amplitude) < 1 := lt_of_not_ge h
  have hprod : 0 <
      (1 - Real.sqrt (lowerRadicand amplitude)) *
        (1 + Real.sqrt (lowerRadicand amplitude)) :=
    mul_pos (by linarith) (by linarith)
  unfold lowerRadicand at hr0 hr1 hprod hrsq
  nlinarith [sq_nonneg (1 - amplitude)]

lemma upperRoot_ge_one (amplitude : ℝ) :
    1 ≤ Real.sqrt (upperRadicand amplitude) := by
  have hr0 := Real.sqrt_nonneg (upperRadicand amplitude)
  have hrsq := upperRoot_sq amplitude
  by_contra h
  have hr1 : Real.sqrt (upperRadicand amplitude) < 1 := lt_of_not_ge h
  have hprod : 0 <
      (1 - Real.sqrt (upperRadicand amplitude)) *
        (1 + Real.sqrt (upperRadicand amplitude)) :=
    mul_pos (by linarith) (by linarith)
  unfold upperRadicand at hr0 hr1 hprod hrsq
  nlinarith [sq_nonneg (1 + amplitude)]

lemma exactDiamondLowerSq_pos
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    0 < exactDiamondLowerSq amplitude := by
  let center : ℝ := 1 - amplitude + amplitude ^ 2
  let radial : ℝ := amplitude * Real.sqrt (lowerRadicand amplitude)
  have hcenter : 0 < center := by
    dsimp [center]
    nlinarith [sq_nonneg (amplitude - 1 / 2)]
  have hradial : 0 ≤ radial :=
    mul_nonneg ha0 (Real.sqrt_nonneg _)
  have hidentity : center ^ 2 - radial ^ 2 = (1 - amplitude) ^ 2 := by
    dsimp [center, radial]
    rw [mul_pow, lowerRoot_sq]
    unfold lowerRadicand
    ring
  have hright : 0 < (1 - amplitude) ^ 2 :=
    sq_pos_of_pos (sub_pos.mpr ha1)
  dsimp [exactDiamondLowerSq, center, radial] at *
  nlinarith

lemma exactDiamondUpperSq_pos
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    0 < exactDiamondUpperSq amplitude := by
  unfold exactDiamondUpperSq
  have := Real.sqrt_nonneg (upperRadicand amplitude)
  nlinarith [sq_nonneg amplitude]

lemma exactDiamondLowerSq_le_axis
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    exactDiamondLowerSq amplitude ≤ (1 - amplitude) ^ 2 := by
  have hroot := lowerRoot_ge_one amplitude
  unfold exactDiamondLowerSq
  nlinarith

theorem cancellingQuadratic_lower_bound
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude)
    (X Y : ℝ) :
    exactDiamondLowerSq amplitude * (X ^ 2 + Y ^ 2) ≤
      X ^ 2 + ((1 - amplitude) * Y - amplitude * X) ^ 2 := by
  by_cases hzero : amplitude = 0
  · subst amplitude
    norm_num [exactDiamondLowerSq]
  · have haPos : 0 < amplitude := lt_of_le_of_ne ha0 (Ne.symm hzero)
    let root : ℝ := Real.sqrt (lowerRadicand amplitude)
    let lambda : ℝ := exactDiamondLowerSq amplitude
    let A : ℝ := 1 + amplitude ^ 2
    have hroot0 : 0 ≤ root := Real.sqrt_nonneg _
    have hA : 0 < A - lambda := by
      dsimp [A, lambda, exactDiamondLowerSq, root]
      nlinarith
    have hdet :
        (A - lambda) * ((1 - amplitude) ^ 2 - lambda) =
          amplitude ^ 2 * (1 - amplitude) ^ 2 := by
      dsimp [A, lambda, exactDiamondLowerSq, root]
      calc
        (1 + amplitude ^ 2 -
              (1 - amplitude + amplitude ^ 2 -
                amplitude * Real.sqrt (lowerRadicand amplitude))) *
            ((1 - amplitude) ^ 2 -
              (1 - amplitude + amplitude ^ 2 -
                amplitude * Real.sqrt (lowerRadicand amplitude))) =
            amplitude ^ 2 *
              (Real.sqrt (lowerRadicand amplitude) ^ 2 - 1) := by ring
        _ = amplitude ^ 2 * (1 - amplitude) ^ 2 := by
          rw [lowerRoot_sq]
          unfold lowerRadicand
          ring
    have hfactor :
        (A - lambda) *
            (X ^ 2 + ((1 - amplitude) * Y - amplitude * X) ^ 2 -
              lambda * (X ^ 2 + Y ^ 2)) =
          ((A - lambda) * X - amplitude * (1 - amplitude) * Y) ^ 2 := by
      nlinarith
    have hsquare := sq_nonneg
      ((A - lambda) * X - amplitude * (1 - amplitude) * Y)
    have hresult : 0 ≤
        X ^ 2 + ((1 - amplitude) * Y - amplitude * X) ^ 2 -
          lambda * (X ^ 2 + Y ^ 2) := by
      nlinarith [hfactor, hsquare]
    simpa [lambda] using hresult

theorem reinforcingQuadratic_upper_bound
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude)
    (X Y : ℝ) :
    X ^ 2 + (amplitude * X + (1 + amplitude) * Y) ^ 2 ≤
      exactDiamondUpperSq amplitude * (X ^ 2 + Y ^ 2) := by
  by_cases hzero : amplitude = 0
  · subst amplitude
    norm_num [exactDiamondUpperSq]
  · have haPos : 0 < amplitude := lt_of_le_of_ne ha0 (Ne.symm hzero)
    let root : ℝ := Real.sqrt (upperRadicand amplitude)
    let lambda : ℝ := exactDiamondUpperSq amplitude
    let A : ℝ := 1 + amplitude ^ 2
    have hroot0 : 0 ≤ root := Real.sqrt_nonneg _
    have hA : 0 < lambda - A := by
      dsimp [A, lambda, exactDiamondUpperSq, root]
      nlinarith
    have hdet :
        (lambda - A) * (lambda - (1 + amplitude) ^ 2) =
          amplitude ^ 2 * (1 + amplitude) ^ 2 := by
      dsimp [A, lambda, exactDiamondUpperSq, root]
      calc
        (1 + amplitude + amplitude ^ 2 +
              amplitude * Real.sqrt (upperRadicand amplitude) -
              (1 + amplitude ^ 2)) *
            (1 + amplitude + amplitude ^ 2 +
              amplitude * Real.sqrt (upperRadicand amplitude) -
              (1 + amplitude) ^ 2) =
            amplitude ^ 2 *
              (Real.sqrt (upperRadicand amplitude) ^ 2 - 1) := by ring
        _ = amplitude ^ 2 * (1 + amplitude) ^ 2 := by
          rw [upperRoot_sq]
          unfold upperRadicand
          ring
    have hfactor :
        (lambda - A) *
            (lambda * (X ^ 2 + Y ^ 2) -
              (X ^ 2 + (amplitude * X + (1 + amplitude) * Y) ^ 2)) =
          ((lambda - A) * X - amplitude * (1 + amplitude) * Y) ^ 2 := by
      nlinarith
    have hsquare := sq_nonneg
      ((lambda - A) * X - amplitude * (1 + amplitude) * Y)
    have hresult : 0 ≤
        lambda * (X ^ 2 + Y ^ 2) -
          (X ^ 2 + (amplitude * X + (1 + amplitude) * Y) ^ 2) := by
      nlinarith [hfactor, hsquare]
    simpa [lambda] using hresult

theorem exactDiamond_upper_bound
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude)
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalDiamondBand) :
    forwardBlowUpSq amplitude point ≤ exactDiamondUpperSq amplitude := by
  rcases diamond_unit_and_slope hpoint with ⟨hunit, hslope⟩
  let x : ℝ := point.1.ofLp 0
  let y : ℝ := point.1.ofLp 1
  let s : ℝ := point.2
  let X : ℝ := |x|
  let Y : ℝ := |y|
  let z : ℝ := y + amplitude * s
  have hz : |z| ≤ amplitude * X + (1 + amplitude) * Y := by
    calc
      |z| = |y + amplitude * s| := rfl
      _ ≤ |y| + |amplitude * s| := abs_add_le _ _
      _ = Y + amplitude * |s| := by
        dsimp [Y]
        rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ Y + amplitude * (X + Y) := by
        simpa [X, Y, s] using
          add_le_add_left (mul_le_mul_of_nonneg_left hslope ha0) Y
      _ = amplitude * X + (1 + amplitude) * Y := by ring
  have hright0 : 0 ≤ amplitude * X + (1 + amplitude) * Y := by
    dsimp [X, Y]
    positivity
  have hzsq : z ^ 2 ≤
      (amplitude * X + (1 + amplitude) * Y) ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg z) hright0).2 hz
    simpa [sq_abs] using this
  have hspectral := reinforcingQuadratic_upper_bound ha0 X Y
  have hunitAbs : X ^ 2 + Y ^ 2 = 1 := by
    dsimp [X, Y, x, y]
    simpa [sq_abs] using hunit
  have hxSq : X ^ 2 = x ^ 2 := by simp [X, sq_abs]
  dsimp [forwardBlowUpSq, x, y, s, z] at *
  nlinarith

theorem exactDiamond_lower_bound
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1)
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalDiamondBand) :
    exactDiamondLowerSq amplitude ≤ forwardBlowUpSq amplitude point := by
  rcases diamond_unit_and_slope hpoint with ⟨hunit, hslope⟩
  let x : ℝ := point.1.ofLp 0
  let y : ℝ := point.1.ofLp 1
  let s : ℝ := point.2
  let X : ℝ := |x|
  let Y : ℝ := |y|
  let z : ℝ := y + amplitude * s
  have hX0 : 0 ≤ X := abs_nonneg x
  have hY0 : 0 ≤ Y := abs_nonneg y
  have hunitAbs : X ^ 2 + Y ^ 2 = 1 := by
    dsimp [X, Y, x, y]
    simpa [sq_abs] using hunit
  have hxSq : X ^ 2 = x ^ 2 := by simp [X, sq_abs]
  have hyBridge : Y ≤ |z| + amplitude * (X + Y) := by
    calc
      Y = |z - amplitude * s| := by
        dsimp [Y, z, y]
        congr 1
        ring
      _ ≤ |z| + |amplitude * s| := abs_sub _ _
      _ = |z| + amplitude * |s| := by
        rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ |z| + amplitude * (X + Y) := by
        simpa [X, Y, s] using
          add_le_add_left (mul_le_mul_of_nonneg_left hslope ha0) |z|
  by_cases hcancel : Y ≤ amplitude * (X + Y)
  · have hrelation : (1 - amplitude) * Y ≤ amplitude * X := by
      nlinarith
    have hleft0 : 0 ≤ (1 - amplitude) * Y :=
      mul_nonneg (sub_nonneg.mpr (le_of_lt ha1)) hY0
    have hright0 : 0 ≤ amplitude * X := mul_nonneg ha0 hX0
    have hsquare : ((1 - amplitude) * Y) ^ 2 ≤
        (amplitude * X) ^ 2 :=
      (sq_le_sq₀ hleft0 hright0).2 hrelation
    have hpoly : (amplitude - 1) * amplitude ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) ha0
    have hden : amplitude ^ 2 + (1 - amplitude) ^ 2 ≤ 1 := by
      nlinarith
    have hdenX := mul_le_mul_of_nonneg_right hden (sq_nonneg X)
    have haxis : (1 - amplitude) ^ 2 ≤ X ^ 2 := by
      nlinarith
    have hlambda := exactDiamondLowerSq_le_axis ha0
    have hz0 := sq_nonneg z
    dsimp [forwardBlowUpSq, x, y, s, z] at *
    nlinarith
  · have hstrict : amplitude * (X + Y) < Y := lt_of_not_ge hcancel
    have hminimum0 : 0 ≤ (1 - amplitude) * Y - amplitude * X := by
      nlinarith
    have hminimum : (1 - amplitude) * Y - amplitude * X ≤ |z| := by
      nlinarith
    have hsq : ((1 - amplitude) * Y - amplitude * X) ^ 2 ≤ z ^ 2 := by
      have := (sq_le_sq₀ hminimum0 (abs_nonneg z)).2 hminimum
      simpa [sq_abs] using this
    have hspectral := cancellingQuadratic_lower_bound ha0 X Y
    dsimp [forwardBlowUpSq, x, y, s, z] at *
    nlinarith

/-! ### Explicit extremizing directions -/

def rawNorm (X Y : ℝ) : ℝ := Real.sqrt (X ^ 2 + Y ^ 2)

def normalizedPositiveDirection (X Y : ℝ) : AmbientPlane :=
  planeEmbedding ⟨X / rawNorm X Y, Y / rawNorm X Y⟩

def lowerRawX (amplitude : ℝ) : ℝ := 1 - amplitude

def lowerRawY (amplitude : ℝ) : ℝ :=
  1 + Real.sqrt (lowerRadicand amplitude)

def upperRawX (amplitude : ℝ) : ℝ := 1 + amplitude

def upperRawY (amplitude : ℝ) : ℝ :=
  1 + Real.sqrt (upperRadicand amplitude)

def lowerExtremizingDirection (amplitude : ℝ) : AmbientPlane :=
  normalizedPositiveDirection (lowerRawX amplitude) (lowerRawY amplitude)

def upperExtremizingDirection (amplitude : ℝ) : AmbientPlane :=
  normalizedPositiveDirection (upperRawX amplitude) (upperRawY amplitude)

def lowerDiamondWitness (amplitude : ℝ) : BlowUpPoint :=
  (lowerExtremizingDirection amplitude,
    -(lowerExtremizingDirection amplitude).ofLp 0 -
      (lowerExtremizingDirection amplitude).ofLp 1)

def upperDiamondWitness (amplitude : ℝ) : BlowUpPoint :=
  (upperExtremizingDirection amplitude,
    (upperExtremizingDirection amplitude).ofLp 0 +
      (upperExtremizingDirection amplitude).ofLp 1)

lemma rawNorm_sq
    {X Y : ℝ} (hsum : 0 ≤ X ^ 2 + Y ^ 2) :
    rawNorm X Y ^ 2 = X ^ 2 + Y ^ 2 := by
  exact Real.sq_sqrt hsum

lemma rawNorm_pos
    {X Y : ℝ} (hsum : 0 < X ^ 2 + Y ^ 2) :
    0 < rawNorm X Y := by
  exact Real.sqrt_pos.2 hsum

lemma normalizedPositiveDirection_mem_sphere
    {X Y : ℝ} (hsum : 0 < X ^ 2 + Y ^ 2) :
    normalizedPositiveDirection X Y ∈ Metric.sphere kernelOrigin 1 := by
  have hnorm_pos := rawNorm_pos hsum
  have hnorm_ne : rawNorm X Y ≠ 0 := ne_of_gt hnorm_pos
  have hnorm_sq := rawNorm_sq (le_of_lt hsum)
  rw [Metric.mem_sphere, dist_comm]
  have hsquare :
      dist kernelOrigin (normalizedPositiveDirection X Y) ^ 2 = 1 := by
    rw [dist_sq_eq_coordinate_sq_sum]
    simp [kernelOrigin, normalizedPositiveDirection, planeEmbedding]
    field_simp [hnorm_ne]
    nlinarith
  have hdist0 : 0 ≤ dist kernelOrigin (normalizedPositiveDirection X Y) :=
    dist_nonneg
  nlinarith

lemma normalizedPositiveDirection_unit
    {X Y : ℝ} (hsum : 0 < X ^ 2 + Y ^ 2) :
    (normalizedPositiveDirection X Y).ofLp 0 ^ 2 +
      (normalizedPositiveDirection X Y).ofLp 1 ^ 2 = 1 := by
  have hnorm_pos := rawNorm_pos hsum
  have hnorm_ne : rawNorm X Y ≠ 0 := ne_of_gt hnorm_pos
  have hnorm_sq := rawNorm_sq (le_of_lt hsum)
  simp [normalizedPositiveDirection, planeEmbedding]
  field_simp [hnorm_ne]
  nlinarith

lemma normalizedPositiveDirection_width_le_sqrt_two
    {X Y : ℝ} (hsum : 0 < X ^ 2 + Y ^ 2) :
    |(normalizedPositiveDirection X Y).ofLp 0| +
        |(normalizedPositiveDirection X Y).ofLp 1| ≤ Real.sqrt 2 := by
  have hunit := normalizedPositiveDirection_unit hsum
  have hwidth0 : 0 ≤
      |(normalizedPositiveDirection X Y).ofLp 0| +
        |(normalizedPositiveDirection X Y).ofLp 1| := by positivity
  have hwidthSq :
      (|(normalizedPositiveDirection X Y).ofLp 0| +
          |(normalizedPositiveDirection X Y).ofLp 1|) ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg
      (|(normalizedPositiveDirection X Y).ofLp 0| -
        |(normalizedPositiveDirection X Y).ofLp 1|),
      sq_abs ((normalizedPositiveDirection X Y).ofLp 0),
      sq_abs ((normalizedPositiveDirection X Y).ofLp 1)]
  nlinarith [sqrt_two_nonneg, sqrt_two_sq]

lemma lower_raw_sum_pos
    {amplitude : ℝ} (ha1 : amplitude < 1) :
    0 < lowerRawX amplitude ^ 2 + lowerRawY amplitude ^ 2 := by
  have hx : 0 < lowerRawX amplitude := by
    unfold lowerRawX
    linarith
  nlinarith [sq_pos_of_pos hx, sq_nonneg (lowerRawY amplitude)]

lemma upper_raw_sum_pos
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    0 < upperRawX amplitude ^ 2 + upperRawY amplitude ^ 2 := by
  have hx : 0 < upperRawX amplitude := by
    unfold upperRawX
    linarith
  nlinarith [sq_pos_of_pos hx, sq_nonneg (upperRawY amplitude)]

lemma lower_direction_coordinates_nonneg
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    0 ≤ (lowerExtremizingDirection amplitude).ofLp 0 ∧
      0 ≤ (lowerExtremizingDirection amplitude).ofLp 1 := by
  have hnorm := le_of_lt (rawNorm_pos (lower_raw_sum_pos ha1))
  constructor
  · simp [lowerExtremizingDirection, normalizedPositiveDirection,
      lowerRawX, planeEmbedding]
    exact div_nonneg (by linarith) hnorm
  · simp [lowerExtremizingDirection, normalizedPositiveDirection,
      lowerRawY, planeEmbedding]
    exact div_nonneg (by positivity) hnorm

lemma upper_direction_coordinates_nonneg
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    0 ≤ (upperExtremizingDirection amplitude).ofLp 0 ∧
      0 ≤ (upperExtremizingDirection amplitude).ofLp 1 := by
  have hnorm := le_of_lt (rawNorm_pos (upper_raw_sum_pos ha0))
  constructor
  · simp [upperExtremizingDirection, normalizedPositiveDirection,
      upperRawX, planeEmbedding]
    exact div_nonneg (by linarith) hnorm
  · simp [upperExtremizingDirection, normalizedPositiveDirection,
      upperRawY, planeEmbedding]
    exact div_nonneg (by positivity) hnorm

lemma lowerDiamondWitness_mem
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    lowerDiamondWitness amplitude ∈ directionalDiamondBand := by
  have hsum := lower_raw_sum_pos ha1
  have hsphere := normalizedPositiveDirection_mem_sphere hsum
  have hwidth := normalizedPositiveDirection_width_le_sqrt_two hsum
  rcases lower_direction_coordinates_nonneg ha0 ha1 with ⟨hx, hy⟩
  have hslope :
      |(lowerDiamondWitness amplitude).2| =
        |(lowerExtremizingDirection amplitude).ofLp 0| +
          |(lowerExtremizingDirection amplitude).ofLp 1| := by
    rw [show (lowerDiamondWitness amplitude).2 =
      -((lowerExtremizingDirection amplitude).ofLp 0 +
        (lowerExtremizingDirection amplitude).ofLp 1) by
          simp [lowerDiamondWitness]; ring]
    rw [abs_neg, abs_of_nonneg (add_nonneg hx hy),
      abs_of_nonneg hx, abs_of_nonneg hy]
  rw [directionalDiamondBand]
  constructor
  · refine ⟨hsphere, ?_⟩
    exact abs_le.mp (hslope.le.trans hwidth)
  · exact hslope.le

lemma upperDiamondWitness_mem
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    upperDiamondWitness amplitude ∈ directionalDiamondBand := by
  have hsum := upper_raw_sum_pos ha0
  have hsphere := normalizedPositiveDirection_mem_sphere hsum
  have hwidth := normalizedPositiveDirection_width_le_sqrt_two hsum
  rcases upper_direction_coordinates_nonneg ha0 with ⟨hx, hy⟩
  have hslope :
      |(upperDiamondWitness amplitude).2| =
        |(upperExtremizingDirection amplitude).ofLp 0| +
          |(upperExtremizingDirection amplitude).ofLp 1| := by
    simp [upperDiamondWitness, abs_of_nonneg hx, abs_of_nonneg hy,
      abs_of_nonneg (add_nonneg hx hy)]
  rw [directionalDiamondBand]
  constructor
  · refine ⟨hsphere, ?_⟩
    exact abs_le.mp (hslope.le.trans hwidth)
  · exact hslope.le

lemma lower_raw_quadratic_identity
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    lowerRawX amplitude ^ 2 +
        ((1 - amplitude) * lowerRawY amplitude -
          amplitude * lowerRawX amplitude) ^ 2 =
      exactDiamondLowerSq amplitude *
        (lowerRawX amplitude ^ 2 + lowerRawY amplitude ^ 2) := by
  by_cases hzero : amplitude = 0
  · subst amplitude
    simp [lowerRawX, lowerRawY, exactDiamondLowerSq]
  · have haPos : 0 < amplitude := lt_of_le_of_ne ha0 (Ne.symm hzero)
    let lambda : ℝ := exactDiamondLowerSq amplitude
    let A : ℝ := 1 + amplitude ^ 2
    have hA : 0 < A - lambda := by
      dsimp [A, lambda, exactDiamondLowerSq]
      nlinarith [Real.sqrt_nonneg (lowerRadicand amplitude)]
    have hdet :
        (A - lambda) * ((1 - amplitude) ^ 2 - lambda) =
          amplitude ^ 2 * (1 - amplitude) ^ 2 := by
      dsimp [A, lambda, exactDiamondLowerSq]
      calc
        (1 + amplitude ^ 2 -
              (1 - amplitude + amplitude ^ 2 -
                amplitude * Real.sqrt (lowerRadicand amplitude))) *
            ((1 - amplitude) ^ 2 -
              (1 - amplitude + amplitude ^ 2 -
                amplitude * Real.sqrt (lowerRadicand amplitude))) =
            amplitude ^ 2 *
              (Real.sqrt (lowerRadicand amplitude) ^ 2 - 1) := by ring
        _ = amplitude ^ 2 * (1 - amplitude) ^ 2 := by
          rw [lowerRoot_sq]
          unfold lowerRadicand
          ring
    have hrelation :
        (A - lambda) * lowerRawX amplitude =
          amplitude * (1 - amplitude) * lowerRawY amplitude := by
      dsimp [A, lambda, exactDiamondLowerSq, lowerRawX, lowerRawY]
      ring
    have hfactor :
        (A - lambda) *
            (lowerRawX amplitude ^ 2 +
                ((1 - amplitude) * lowerRawY amplitude -
                  amplitude * lowerRawX amplitude) ^ 2 -
              lambda *
                (lowerRawX amplitude ^ 2 + lowerRawY amplitude ^ 2)) =
          ((A - lambda) * lowerRawX amplitude -
            amplitude * (1 - amplitude) * lowerRawY amplitude) ^ 2 := by
      nlinarith
    have hsquareZero :
        ((A - lambda) * lowerRawX amplitude -
          amplitude * (1 - amplitude) * lowerRawY amplitude) ^ 2 = 0 := by
      rw [hrelation]
      norm_num
    dsimp [lambda] at hfactor ⊢
    nlinarith

lemma upper_raw_quadratic_identity
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    upperRawX amplitude ^ 2 +
        (amplitude * upperRawX amplitude +
          (1 + amplitude) * upperRawY amplitude) ^ 2 =
      exactDiamondUpperSq amplitude *
        (upperRawX amplitude ^ 2 + upperRawY amplitude ^ 2) := by
  by_cases hzero : amplitude = 0
  · subst amplitude
    simp [upperRawX, upperRawY, exactDiamondUpperSq]
  · have haPos : 0 < amplitude := lt_of_le_of_ne ha0 (Ne.symm hzero)
    let lambda : ℝ := exactDiamondUpperSq amplitude
    let A : ℝ := 1 + amplitude ^ 2
    have hA : 0 < lambda - A := by
      dsimp [A, lambda, exactDiamondUpperSq]
      nlinarith [Real.sqrt_nonneg (upperRadicand amplitude)]
    have hdet :
        (lambda - A) * (lambda - (1 + amplitude) ^ 2) =
          amplitude ^ 2 * (1 + amplitude) ^ 2 := by
      dsimp [A, lambda, exactDiamondUpperSq]
      calc
        (1 + amplitude + amplitude ^ 2 +
              amplitude * Real.sqrt (upperRadicand amplitude) -
              (1 + amplitude ^ 2)) *
            (1 + amplitude + amplitude ^ 2 +
              amplitude * Real.sqrt (upperRadicand amplitude) -
              (1 + amplitude) ^ 2) =
            amplitude ^ 2 *
              (Real.sqrt (upperRadicand amplitude) ^ 2 - 1) := by ring
        _ = amplitude ^ 2 * (1 + amplitude) ^ 2 := by
          rw [upperRoot_sq]
          unfold upperRadicand
          ring
    have hrelation :
        (lambda - A) * upperRawX amplitude =
          amplitude * (1 + amplitude) * upperRawY amplitude := by
      dsimp [A, lambda, exactDiamondUpperSq, upperRawX, upperRawY]
      ring
    have hfactor :
        (lambda - A) *
            (lambda *
                (upperRawX amplitude ^ 2 + upperRawY amplitude ^ 2) -
              (upperRawX amplitude ^ 2 +
                (amplitude * upperRawX amplitude +
                  (1 + amplitude) * upperRawY amplitude) ^ 2)) =
          ((lambda - A) * upperRawX amplitude -
            amplitude * (1 + amplitude) * upperRawY amplitude) ^ 2 := by
      nlinarith
    have hsquareZero :
        ((lambda - A) * upperRawX amplitude -
          amplitude * (1 + amplitude) * upperRawY amplitude) ^ 2 = 0 := by
      rw [hrelation]
      norm_num
    dsimp [lambda] at hfactor ⊢
    nlinarith

theorem lowerDiamondWitness_exact
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    forwardBlowUpSq amplitude (lowerDiamondWitness amplitude) =
      exactDiamondLowerSq amplitude := by
  have hsum := lower_raw_sum_pos ha1
  have hnorm_pos := rawNorm_pos hsum
  have hnorm_ne : rawNorm (lowerRawX amplitude) (lowerRawY amplitude) ≠ 0 :=
    ne_of_gt hnorm_pos
  have hnorm_sq := rawNorm_sq (le_of_lt hsum)
  have hidentity := lower_raw_quadratic_identity ha0
  simp [forwardBlowUpSq, lowerDiamondWitness, lowerExtremizingDirection,
    normalizedPositiveDirection, planeEmbedding]
  field_simp [hnorm_ne]
  nlinarith

theorem upperDiamondWitness_exact
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    forwardBlowUpSq amplitude (upperDiamondWitness amplitude) =
      exactDiamondUpperSq amplitude := by
  have hsum := upper_raw_sum_pos ha0
  have hnorm_pos := rawNorm_pos hsum
  have hnorm_ne : rawNorm (upperRawX amplitude) (upperRawY amplitude) ≠ 0 :=
    ne_of_gt hnorm_pos
  have hnorm_sq := rawNorm_sq (le_of_lt hsum)
  have hidentity := upper_raw_quadratic_identity ha0
  simp [forwardBlowUpSq, upperDiamondWitness, upperExtremizingDirection,
    normalizedPositiveDirection, planeEmbedding]
  field_simp [hnorm_ne]
  nlinarith

theorem exactDiamond_envelope_isSharp
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    IsLeast
        (forwardBlowUpSq amplitude '' directionalDiamondBand)
        (exactDiamondLowerSq amplitude) ∧
      IsGreatest
        (forwardBlowUpSq amplitude '' directionalDiamondBand)
        (exactDiamondUpperSq amplitude) := by
  constructor
  · constructor
    · exact ⟨lowerDiamondWitness amplitude,
        lowerDiamondWitness_mem ha0 ha1, lowerDiamondWitness_exact ha0 ha1⟩
    · rintro _ ⟨point, hpoint, rfl⟩
      exact exactDiamond_lower_bound ha0 ha1 hpoint
  · constructor
    · exact ⟨upperDiamondWitness amplitude,
        upperDiamondWitness_mem ha0, upperDiamondWitness_exact ha0⟩
    · rintro _ ⟨point, hpoint, rfl⟩
      exact exactDiamond_upper_bound ha0 hpoint

/-! ### Sharp reciprocal certificate -/

def sharpDiamondInverseRegularity (amplitude : ℝ) : ℝ :=
  forwardBlowUpSqRegularity amplitude / (exactDiamondLowerSq amplitude) ^ 2

def sharpDiamondInverseMeshTerm (amplitude delta : ℝ) : ℝ :=
  sharpDiamondInverseRegularity amplitude * delta

def sharpDiamondInverseCertificateGap
    (amplitude delta sampleMax : ℝ) : ℝ :=
  sampleMax + sharpDiamondInverseMeshTerm amplitude delta -
    (exactDiamondLowerSq amplitude)⁻¹

theorem certifiedDiamondLowerSq_le_exact
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude) :
    certifiedDiamondLowerSq amplitude ≤ exactDiamondLowerSq amplitude := by
  have hwitness := certifiedDiamond_lower_certificate hadm
    (lowerDiamondWitness_mem hadm.1 (admissibleAmplitude_lt_one hadm))
  rw [lowerDiamondWitness_exact hadm.1 (admissibleAmplitude_lt_one hadm)] at hwitness
  exact hwitness

theorem exactDiamondUpperSq_le_relaxed
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude) :
    exactDiamondUpperSq amplitude ≤ relaxedUpperSq amplitude := by
  have hwitness := (relaxed_envelope hadm
    (diamond_mem_relaxedChamber (upperDiamondWitness_mem hadm.1))).2
  rw [upperDiamondWitness_exact hadm.1] at hwitness
  exact hwitness

theorem exactDiamond_inverse_bounds
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude)
    {point : BlowUpPoint} (hpoint : point ∈ directionalDiamondBand) :
    (exactDiamondUpperSq amplitude)⁻¹ ≤ inverseBlowUpSq amplitude point ∧
      inverseBlowUpSq amplitude point ≤ (exactDiamondLowerSq amplitude)⁻¹ := by
  have hlower := exactDiamond_lower_bound hadm.1
    (admissibleAmplitude_lt_one hadm) hpoint
  have hupper := exactDiamond_upper_bound hadm.1 hpoint
  have hlower_pos := exactDiamondLowerSq_pos hadm.1
    (admissibleAmplitude_lt_one hadm)
  have hforward_pos : 0 < forwardBlowUpSq amplitude point :=
    lt_of_lt_of_le hlower_pos hlower
  have hupper_pos := exactDiamondUpperSq_pos hadm.1
  constructor
  · exact (inv_le_inv₀ hupper_pos hforward_pos).2 hupper
  · exact (inv_le_inv₀ hforward_pos hlower_pos).2 hlower

theorem exactDiamond_inverse_extrema
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude) :
    inverseBlowUpSq amplitude (upperDiamondWitness amplitude) =
        (exactDiamondUpperSq amplitude)⁻¹ ∧
      inverseBlowUpSq amplitude (lowerDiamondWitness amplitude) =
        (exactDiamondLowerSq amplitude)⁻¹ := by
  constructor
  · rw [inverseBlowUpSq, upperDiamondWitness_exact hadm.1]
  · rw [inverseBlowUpSq, lowerDiamondWitness_exact hadm.1
      (admissibleAmplitude_lt_one hadm)]

theorem sharpDiamond_inverse_regularity_bound
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude)
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand) :
    |inverseBlowUpSq amplitude first - inverseBlowUpSq amplitude second| ≤
      sharpDiamondInverseRegularity amplitude * dist first second := by
  have hreg := forwardBlowUpSq_regularity_bound hadm.1 first
    (diamond_mem_relaxedChamber hfirst) second
    (diamond_mem_relaxedChamber hsecond)
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
        forwardBlowUpSqRegularity amplitude * dist first second := by
    simpa [abs_sub_comm] using hreg
  have hregularity_nonneg : 0 ≤ forwardBlowUpSqRegularity amplitude :=
    forwardBlowUpSqRegularity_nonneg hadm.1
  have htarget_nonneg : 0 ≤
      forwardBlowUpSqRegularity amplitude * dist first second :=
    mul_nonneg hregularity_nonneg dist_nonneg
  have hfrac : |forwardBlowUpSq amplitude second -
        forwardBlowUpSq amplitude first| /
      |forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second| ≤
        (forwardBlowUpSqRegularity amplitude * dist first second) /
          exactDiamondLowerSq amplitude ^ 2 :=
    div_le_div₀ htarget_nonneg hnum hlower_sq_pos hden
  change |(forwardBlowUpSq amplitude first)⁻¹ -
      (forwardBlowUpSq amplitude second)⁻¹| ≤ _
  rw [inv_sub_inv hf_pos.ne' hs_pos.ne', abs_div]
  calc
    |forwardBlowUpSq amplitude second - forwardBlowUpSq amplitude first| /
          |forwardBlowUpSq amplitude first * forwardBlowUpSq amplitude second| ≤
        (forwardBlowUpSqRegularity amplitude * dist first second) /
          exactDiamondLowerSq amplitude ^ 2 := hfrac
    _ = sharpDiamondInverseRegularity amplitude * dist first second := by
      unfold sharpDiamondInverseRegularity
      field_simp [ne_of_gt hlower_sq_pos]

lemma sharpDiamondInverseRegularity_nonneg
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude) :
    0 ≤ sharpDiamondInverseRegularity amplitude := by
  unfold sharpDiamondInverseRegularity
  exact div_nonneg (forwardBlowUpSqRegularity_nonneg hadm.1) (sq_nonneg _)

theorem sharpDiamondInverseRegularity_le_certified
    {amplitude : ℝ} (hadm : AdmissibleAmplitude amplitude) :
    sharpDiamondInverseRegularity amplitude ≤
      certifiedDiamondInverseRegularity amplitude := by
  have hnum := forwardBlowUpSqRegularity_nonneg hadm.1
  have hcert_pos := certifiedDiamondLowerSq_pos hadm
  have hexact_pos := exactDiamondLowerSq_pos hadm.1
    (admissibleAmplitude_lt_one hadm)
  have hlower := certifiedDiamondLowerSq_le_exact hadm
  have hsquare : certifiedDiamondLowerSq amplitude ^ 2 ≤
      exactDiamondLowerSq amplitude ^ 2 := by nlinarith
  unfold sharpDiamondInverseRegularity certifiedDiamondInverseRegularity
  exact div_le_div_of_nonneg_left hnum (sq_pos_of_pos hcert_pos) hsquare

theorem sharpDiamondInverseMeshTerm_le_certified
    {amplitude delta : ℝ} (hadm : AdmissibleAmplitude amplitude)
    (hdelta : 0 ≤ delta) :
    sharpDiamondInverseMeshTerm amplitude delta ≤
      certifiedDiamondInverseMeshTerm amplitude delta := by
  unfold sharpDiamondInverseMeshTerm certifiedDiamondInverseMeshTerm
  exact mul_le_mul_of_nonneg_right
    (sharpDiamondInverseRegularity_le_certified hadm) hdelta

theorem half_amplitude_exact_stronger :
    certifiedDiamondLowerSq (1 / 2 : ℝ) <
      exactDiamondLowerSq (1 / 2 : ℝ) := by
  rw [half_amplitude_certifiedLower_exact]
  have hr0 := Real.sqrt_nonneg (lowerRadicand (1 / 2 : ℝ))
  have hrsq := lowerRoot_sq (1 / 2 : ℝ)
  norm_num [diamondLowerSq, exactDiamondLowerSq, lowerRadicand] at *
  nlinarith

theorem half_amplitude_sharpRegularity_strict :
    sharpDiamondInverseRegularity (1 / 2 : ℝ) <
      certifiedDiamondInverseRegularity (1 / 2 : ℝ) := by
  have hcert_pos : 0 < certifiedDiamondLowerSq (1 / 2 : ℝ) :=
    certifiedDiamondLowerSq_pos half_amplitude_admissible
  have hexact_pos : 0 < exactDiamondLowerSq (1 / 2 : ℝ) :=
    exactDiamondLowerSq_pos (by norm_num) (by norm_num)
  have hsquare : certifiedDiamondLowerSq (1 / 2 : ℝ) ^ 2 <
      exactDiamondLowerSq (1 / 2 : ℝ) ^ 2 := by
    nlinarith [half_amplitude_exact_stronger]
  have hnum_pos : 0 < forwardBlowUpSqRegularity (1 / 2 : ℝ) := by
    unfold forwardBlowUpSqRegularity
    norm_num
  unfold sharpDiamondInverseRegularity certifiedDiamondInverseRegularity
  rw [div_lt_div_iff₀ (sq_pos_of_pos hexact_pos) (sq_pos_of_pos hcert_pos)]
  exact mul_lt_mul_of_pos_left hsquare hnum_pos

theorem half_amplitude_sharpMeshTerm_strict
    {delta : ℝ} (hdelta : 0 < delta) :
    sharpDiamondInverseMeshTerm (1 / 2 : ℝ) delta <
      certifiedDiamondInverseMeshTerm (1 / 2 : ℝ) delta := by
  unfold sharpDiamondInverseMeshTerm certifiedDiamondInverseMeshTerm
  exact mul_lt_mul_of_pos_right half_amplitude_sharpRegularity_strict hdelta

theorem exists_sharp_inverse_diamond_finiteCertificate
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
          (sharpDiamondInverseRegularity amplitude)
          (inverseBlowUpSq amplitude) ∧
      (∀ point ∈ directionalDiamondBand,
        inverseBlowUpSq amplitude point ≤
          IntrinsicNonradialShearDeltaNet.noisySampleUpper sample +
            sharpDiamondInverseMeshTerm amplitude delta) ∧
      0 ≤ sharpDiamondInverseCertificateGap amplitude delta
        (IntrinsicNonradialShearDeltaNet.noisySampleUpper sample) ∧
      sharpDiamondInverseCertificateGap amplitude delta
          (IntrinsicNonradialShearDeltaNet.noisySampleUpper sample) ≤
        sharpDiamondInverseMeshTerm amplitude delta := by
  classical
  let value : BlowUpPoint → ℝ := inverseBlowUpSq amplitude
  rcases IntrinsicNonradialShearClosedCore.finiteMetricDeltaNet_of_compact
      directionalDiamondBand_compact hdelta with
    ⟨centers, hfinite, hcenters_inside, hcenters_cover⟩
  let centersFinset := hfinite.toFinset
  let sample := centersFinset.toList.map
    (IntrinsicNonradialShearClosedCore.exactUpperReading value)
  have hexact : ∀ reading ∈ sample,
      reading.measured = value reading.point ∧ reading.error = 0 := by
    intro reading hreading
    rcases List.mem_map.mp hreading with ⟨center, hcenter, rfl⟩
    simp [IntrinsicNonradialShearClosedCore.exactUpperReading]
  have hvalid : IntrinsicNonradialShearDeltaNet.NoisyUpperSampleValid
      value sample := by
    intro reading hreading
    have hreading_exact := hexact reading hreading
    rw [hreading_exact.1, hreading_exact.2]
    norm_num
  have hcoverage : IntrinsicNonradialShearDeltaNet.DeltaCoverage
      directionalDiamondBand sample delta := by
    intro point hpoint
    rcases hcenters_cover point hpoint with ⟨center, hcenter, hdist⟩
    refine ⟨IntrinsicNonradialShearClosedCore.exactUpperReading value center, ?_, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨center, ?_, rfl⟩
      simpa [centersFinset] using hcenter
    · simpa [IntrinsicNonradialShearClosedCore.exactUpperReading] using le_of_lt hdist
  have hinside : IntrinsicNonradialShearClosedCore.SampleInside
      directionalDiamondBand sample := by
    intro reading hreading
    rcases List.mem_map.mp hreading with ⟨center, hcenter, rfl⟩
    change center ∈ directionalDiamondBand
    apply hcenters_inside
    simpa [centersFinset] using hcenter
  have hregular : IntrinsicNonradialShearDeltaNet.RegularityCertificate
      directionalDiamondBand sample
      (sharpDiamondInverseRegularity amplitude) value := by
    intro point hpoint reading hreading
    exact sharpDiamond_inverse_regularity_bound hadm hpoint
      (hinside reading hreading)
  have hglobal : ∀ point ∈ directionalDiamondBand,
      value point ≤ IntrinsicNonradialShearDeltaNet.noisySampleUpper sample +
        sharpDiamondInverseMeshTerm amplitude delta := by
    intro point hpoint
    simpa [sharpDiamondInverseMeshTerm] using
      IntrinsicNonradialShearDeltaNet.global_le_noisySampleUpper_add_regularity
        (sharpDiamondInverseRegularity_nonneg hadm)
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
  have hgap_nonneg : 0 ≤ sharpDiamondInverseCertificateGap amplitude delta
      (IntrinsicNonradialShearDeltaNet.noisySampleUpper sample) := by
    change inverseBlowUpSq amplitude (lowerDiamondWitness amplitude) ≤ _
      at hglobal_at_witness
    rw [hwitness] at hglobal_at_witness
    simp only [sharpDiamondInverseCertificateGap]
    linarith
  have hgap_upper : sharpDiamondInverseCertificateGap amplitude delta
        (IntrinsicNonradialShearDeltaNet.noisySampleUpper sample) ≤
      sharpDiamondInverseMeshTerm amplitude delta := by
    simp only [sharpDiamondInverseCertificateGap]
    linarith
  exact ⟨sample, hvalid, hcoverage, hinside, hexact, hregular, hglobal,
    hgap_nonneg, hgap_upper⟩
end

end BoundaryOfSelf.IntrinsicNonradialShearSharpEnvelope
