import IntrinsicNonradialShearCircleCoupling

open scoped Topology RealInnerProductSpace
open Set Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearCircleAsymptotic

noncomputable section

open StandardHausdorffMetricBridge
open LocalSegmentRealCompletion
open IntrinsicNonradialShearExactSupport
open IntrinsicNonradialShearSpectralMap
open IntrinsicNonradialShearKernelSharp
open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearRealizableClosure
open IntrinsicNonradialShearRealizableCertificate
open IntrinsicNonradialShearSharpEnvelope
open IntrinsicNonradialShearSlopeEnvelope
open IntrinsicNonradialShearCircleCoupling

/-! ## IF-BS-22F-F8C20: asymptotic circle witnesses -/

def circleWitnessNorm (t : ℝ) : ℝ :=
  Real.sqrt ((1 + t) ^ 2 + (1 - t) ^ 2)

def circleWitnessFirst (t : ℝ) : AmbientPlane :=
  planeEmbedding
    ({ x := (1 + t) / circleWitnessNorm t
       y := (1 - t) / circleWitnessNorm t } : RealPlanePoint)

def circleWitnessSecond (t : ℝ) : AmbientPlane :=
  planeEmbedding
    ({ x := (1 - t) / circleWitnessNorm t
       y := (1 + t) / circleWitnessNorm t } : RealPlanePoint)

lemma circleWitnessRadicand_pos (t : ℝ) :
    0 < (1 + t) ^ 2 + (1 - t) ^ 2 := by
  nlinarith [sq_nonneg t]

lemma circleWitnessNorm_pos (t : ℝ) :
    0 < circleWitnessNorm t :=
  Real.sqrt_pos.2 (circleWitnessRadicand_pos t)

lemma circleWitnessNorm_sq (t : ℝ) :
    circleWitnessNorm t ^ 2 = 2 * (1 + t ^ 2) := by
  rw [circleWitnessNorm,
    Real.sq_sqrt (le_of_lt (circleWitnessRadicand_pos t))]
  ring

lemma circleWitnessFirst_unit (t : ℝ) :
    (circleWitnessFirst t).ofLp 0 ^ 2 +
      (circleWitnessFirst t).ofLp 1 ^ 2 = 1 := by
  have hnorm_ne : circleWitnessNorm t ≠ 0 :=
    ne_of_gt (circleWitnessNorm_pos t)
  have hnorm_sq := circleWitnessNorm_sq t
  simp [circleWitnessFirst, planeEmbedding]
  field_simp [hnorm_ne]
  nlinarith

lemma circleWitnessSecond_unit (t : ℝ) :
    (circleWitnessSecond t).ofLp 0 ^ 2 +
      (circleWitnessSecond t).ofLp 1 ^ 2 = 1 := by
  have hnorm_ne : circleWitnessNorm t ≠ 0 :=
    ne_of_gt (circleWitnessNorm_pos t)
  have hnorm_sq := circleWitnessNorm_sq t
  simp [circleWitnessSecond, planeEmbedding]
  field_simp [hnorm_ne]
  nlinarith

lemma circleWitnessFirst_mem_sphere (t : ℝ) :
    circleWitnessFirst t ∈ Metric.sphere kernelOrigin 1 := by
  rw [Metric.mem_sphere, dist_comm]
  have hdistSq :=
    dist_sq_eq_coordinate_sq_sum kernelOrigin (circleWitnessFirst t)
  have hunit := circleWitnessFirst_unit t
  have hx0 : kernelOrigin.ofLp 0 = 0 := by simp [kernelOrigin, planeEmbedding]
  have hy0 : kernelOrigin.ofLp 1 = 0 := by simp [kernelOrigin, planeEmbedding]
  rw [hx0, hy0] at hdistSq
  simp only [zero_sub, neg_sq] at hdistSq
  have hsq : dist kernelOrigin (circleWitnessFirst t) ^ 2 = 1 := by
    nlinarith
  nlinarith [(dist_nonneg :
    0 ≤ dist kernelOrigin (circleWitnessFirst t))]

lemma circleWitnessSecond_mem_sphere (t : ℝ) :
    circleWitnessSecond t ∈ Metric.sphere kernelOrigin 1 := by
  rw [Metric.mem_sphere, dist_comm]
  have hdistSq :=
    dist_sq_eq_coordinate_sq_sum kernelOrigin (circleWitnessSecond t)
  have hunit := circleWitnessSecond_unit t
  have hx0 : kernelOrigin.ofLp 0 = 0 := by simp [kernelOrigin, planeEmbedding]
  have hy0 : kernelOrigin.ofLp 1 = 0 := by simp [kernelOrigin, planeEmbedding]
  rw [hx0, hy0] at hdistSq
  simp only [zero_sub, neg_sq] at hdistSq
  have hsq : dist kernelOrigin (circleWitnessSecond t) ^ 2 = 1 := by
    nlinarith
  nlinarith [(dist_nonneg :
    0 ≤ dist kernelOrigin (circleWitnessSecond t))]

theorem circleWitness_xSquare_difference (t : ℝ) :
    (circleWitnessFirst t).ofLp 0 ^ 2 -
        (circleWitnessSecond t).ofLp 0 ^ 2 =
      2 * t / (1 + t ^ 2) := by
  have hnorm_ne : circleWitnessNorm t ≠ 0 :=
    ne_of_gt (circleWitnessNorm_pos t)
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  have hnorm_sq := circleWitnessNorm_sq t
  simp [circleWitnessFirst, circleWitnessSecond, planeEmbedding]
  field_simp [hnorm_ne, hden]
  nlinarith

theorem circleWitness_dist_sq (t : ℝ) :
    dist (circleWitnessFirst t) (circleWitnessSecond t) ^ 2 =
      4 * t ^ 2 / (1 + t ^ 2) := by
  have hnorm_ne : circleWitnessNorm t ≠ 0 :=
    ne_of_gt (circleWitnessNorm_pos t)
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  have hnorm_sq := circleWitnessNorm_sq t
  rw [dist_sq_eq_coordinate_sq_sum]
  simp [circleWitnessFirst, circleWitnessSecond, planeEmbedding]
  field_simp [hnorm_ne, hden]
  nlinarith

lemma circleWitness_dist_pos
    {t : ℝ} (ht : 0 < t) :
    0 < dist (circleWitnessFirst t) (circleWitnessSecond t) := by
  have hden : 0 < 1 + t ^ 2 := by positivity
  have hsq := circleWitness_dist_sq t
  have hright : 0 < 4 * t ^ 2 / (1 + t ^ 2) := by positivity
  nlinarith [(dist_nonneg :
    0 ≤ dist (circleWitnessFirst t) (circleWitnessSecond t))]

lemma circleWitness_xSquare_difference_pos
    {t : ℝ} (ht : 0 < t) :
    0 < (circleWitnessFirst t).ofLp 0 ^ 2 -
      (circleWitnessSecond t).ofLp 0 ^ 2 := by
  rw [circleWitness_xSquare_difference]
  positivity

theorem circleWitness_ratio_exceeds
    {constant t : ℝ}
    (hc0 : 0 ≤ constant) (ht : 0 < t)
    (hscale : constant ^ 2 * (1 + t ^ 2) < 1) :
    constant * dist (circleWitnessFirst t) (circleWitnessSecond t) <
      |(circleWitnessFirst t).ofLp 0 ^ 2 -
        (circleWitnessSecond t).ofLp 0 ^ 2| := by
  have hden : 0 < 1 + t ^ 2 := by positivity
  have hdist0 :
      0 ≤ dist (circleWitnessFirst t) (circleWitnessSecond t) := dist_nonneg
  have hleft0 :
      0 ≤ constant * dist (circleWitnessFirst t) (circleWitnessSecond t) :=
    mul_nonneg hc0 hdist0
  have hdelta := circleWitness_xSquare_difference t
  have hdeltapos := circleWitness_xSquare_difference_pos ht
  rw [abs_of_pos hdeltapos]
  have hdistSq := circleWitness_dist_sq t
  have hsquare :
      (constant * dist (circleWitnessFirst t) (circleWitnessSecond t)) ^ 2 <
        ((circleWitnessFirst t).ofLp 0 ^ 2 -
          (circleWitnessSecond t).ofLp 0 ^ 2) ^ 2 := by
    rw [mul_pow, hdistSq, hdelta]
    field_simp
    nlinarith [sq_pos_of_pos ht]
  nlinarith

def CircleSquareLipschitzConstants : Set ℝ :=
  { constant | ∀ first ∈ Metric.sphere kernelOrigin 1,
      ∀ second ∈ Metric.sphere kernelOrigin 1,
        |first.ofLp 0 ^ 2 - second.ofLp 0 ^ 2| ≤
          constant * dist first second }

theorem circle_xSquare_coefficient_one_isLeast :
    IsLeast CircleSquareLipschitzConstants 1 := by
  constructor
  · intro first hfirst second hsecond
    simpa using circle_xSquare_bound hfirst hsecond
  · intro constant hconstant
    change ∀ first ∈ Metric.sphere kernelOrigin 1,
      ∀ second ∈ Metric.sphere kernelOrigin 1,
        |first.ofLp 0 ^ 2 - second.ofLp 0 ^ 2| ≤
          constant * dist first second at hconstant
    by_contra hnot
    have hc1 : constant < 1 := lt_of_not_ge hnot
    by_cases hcneg : constant < 0
    · let t : ℝ := 1 / 2
      have ht : 0 < t := by norm_num [t]
      have hbound := hconstant
        (circleWitnessFirst t) (circleWitnessFirst_mem_sphere t)
        (circleWitnessSecond t) (circleWitnessSecond_mem_sphere t)
      have hdelta := circleWitness_xSquare_difference_pos ht
      have hdist := circleWitness_dist_pos ht
      have hright :
          constant * dist (circleWitnessFirst t) (circleWitnessSecond t) < 0 :=
        mul_neg_of_neg_of_pos hcneg hdist
      rw [abs_of_pos hdelta] at hbound
      linarith
    · have hc0 : 0 ≤ constant := le_of_not_gt hcneg
      have hcsq1 : constant ^ 2 < 1 := by nlinarith
      let q : ℝ := constant ^ 2
      let d : ℝ := 1 - q
      let t : ℝ := d / 2
      have hq0 : 0 ≤ q := by dsimp [q]; positivity
      have hq1 : q < 1 := by simpa [q] using hcsq1
      have hdpos : 0 < d := by dsimp [d]; linarith
      have hdle : d ≤ 1 := by dsimp [d]; linarith
      have ht : 0 < t := by dsimp [t]; positivity
      have hqdlt : q * d < 1 := by
        calc
          q * d ≤ q * 1 := mul_le_mul_of_nonneg_left hdle hq0
          _ < 1 := by simpa using hq1
      have hsecond : 0 < 1 - q * d / 4 := by linarith
      have hfactor :
          1 - q * (1 + (d / 2) ^ 2) =
            d * (1 - q * d / 4) := by
        dsimp [d]
        ring
      have hscale : constant ^ 2 * (1 + t ^ 2) < 1 := by
        have hpositive : 0 < 1 - q * (1 + (d / 2) ^ 2) := by
          rw [hfactor]
          exact mul_pos hdpos hsecond
        dsimp [q, t] at *
        linarith
      have hexceeds := circleWitness_ratio_exceeds hc0 ht hscale
      have hbound := hconstant
        (circleWitnessFirst t) (circleWitnessFirst_mem_sphere t)
        (circleWitnessSecond t) (circleWitnessSecond_mem_sphere t)
      linarith

lemma unit_width_le_sqrt_two
    {direction : AmbientPlane}
    (hunit : direction.ofLp 0 ^ 2 + direction.ofLp 1 ^ 2 = 1) :
    |direction.ofLp 0| + |direction.ofLp 1| ≤ Real.sqrt 2 := by
  have hsum0 : 0 ≤ |direction.ofLp 0| + |direction.ofLp 1| := by positivity
  have hsquare :
      (|direction.ofLp 0| + |direction.ofLp 1|) ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg (|direction.ofLp 0| - |direction.ofLp 1|),
      sq_abs (direction.ofLp 0), sq_abs (direction.ofLp 1)]
  nlinarith [Real.sqrt_nonneg 2,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

def circleLiftFirst (t : ℝ) : BlowUpPoint :=
  (circleWitnessFirst t,
    (circleWitnessFirst t).ofLp 0 + (circleWitnessFirst t).ofLp 1)

def circleLiftSecond (t : ℝ) : BlowUpPoint :=
  (circleWitnessSecond t,
    (circleWitnessSecond t).ofLp 0 + (circleWitnessSecond t).ofLp 1)

lemma circleLiftFirst_mem
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    circleLiftFirst t ∈ (directionalDiamondBand : Set BlowUpPoint) := by
  have hnorm0 : 0 ≤ circleWitnessNorm t :=
    le_of_lt (circleWitnessNorm_pos t)
  have hx : 0 ≤ (circleWitnessFirst t).ofLp 0 := by
    simp [circleWitnessFirst, planeEmbedding]
    exact div_nonneg (by linarith) hnorm0
  have hy : 0 ≤ (circleWitnessFirst t).ofLp 1 := by
    simp [circleWitnessFirst, planeEmbedding]
    exact div_nonneg (by linarith) hnorm0
  have hwidth := unit_width_le_sqrt_two (circleWitnessFirst_unit t)
  have hslope :
      |(circleLiftFirst t).2| =
        |(circleWitnessFirst t).ofLp 0| +
          |(circleWitnessFirst t).ofLp 1| := by
    simp [circleLiftFirst, abs_of_nonneg hx, abs_of_nonneg hy,
      abs_of_nonneg (add_nonneg hx hy)]
  rw [directionalDiamondBand]
  constructor
  · refine ⟨circleWitnessFirst_mem_sphere t, ?_⟩
    exact abs_le.mp (hslope.le.trans hwidth)
  · exact hslope.le

lemma circleLiftSecond_mem
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    circleLiftSecond t ∈ (directionalDiamondBand : Set BlowUpPoint) := by
  have hnorm0 : 0 ≤ circleWitnessNorm t :=
    le_of_lt (circleWitnessNorm_pos t)
  have hx : 0 ≤ (circleWitnessSecond t).ofLp 0 := by
    simp [circleWitnessSecond, planeEmbedding]
    exact div_nonneg (by linarith) hnorm0
  have hy : 0 ≤ (circleWitnessSecond t).ofLp 1 := by
    simp [circleWitnessSecond, planeEmbedding]
    exact div_nonneg (by linarith) hnorm0
  have hwidth := unit_width_le_sqrt_two (circleWitnessSecond_unit t)
  have hslope :
      |(circleLiftSecond t).2| =
        |(circleWitnessSecond t).ofLp 0| +
          |(circleWitnessSecond t).ofLp 1| := by
    simp [circleLiftSecond, abs_of_nonneg hx, abs_of_nonneg hy,
      abs_of_nonneg (add_nonneg hx hy)]
  rw [directionalDiamondBand]
  constructor
  · refine ⟨circleWitnessSecond_mem_sphere t, ?_⟩
    exact abs_le.mp (hslope.le.trans hwidth)
  · exact hslope.le

lemma circleLift_slopes_equal (t : ℝ) :
    (circleLiftFirst t).2 = (circleLiftSecond t).2 := by
  have hnorm_ne : circleWitnessNorm t ≠ 0 :=
    ne_of_gt (circleWitnessNorm_pos t)
  simp [circleLiftFirst, circleLiftSecond, circleWitnessFirst,
    circleWitnessSecond, planeEmbedding]
  field_simp [hnorm_ne]
  ring

theorem circleLift_dist_sq (t : ℝ) :
    dist (circleLiftFirst t) (circleLiftSecond t) ^ 2 =
      4 * t ^ 2 / (1 + t ^ 2) := by
  rw [Prod.dist_eq]
  have hslope := circleLift_slopes_equal t
  rw [hslope]
  simp
  exact circleWitness_dist_sq t

theorem circleLift_forward_cancellation
    (amplitude t : ℝ) :
    forwardBlowUpSq amplitude (circleLiftFirst t) -
        forwardBlowUpSq amplitude (circleLiftSecond t) =
      -4 * amplitude * t / (1 + t ^ 2) := by
  have hnorm_ne : circleWitnessNorm t ≠ 0 :=
    ne_of_gt (circleWitnessNorm_pos t)
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  have hnorm_sq := circleWitnessNorm_sq t
  simp [forwardBlowUpSq, circleLiftFirst, circleLiftSecond,
    circleWitnessFirst, circleWitnessSecond, planeEmbedding]
  field_simp [hnorm_ne, hden]
  nlinarith

theorem circleLift_forward_cancellation_abs
    {amplitude t : ℝ} (ha0 : 0 ≤ amplitude) (ht0 : 0 ≤ t) :
    |forwardBlowUpSq amplitude (circleLiftFirst t) -
        forwardBlowUpSq amplitude (circleLiftSecond t)| =
      4 * amplitude * t / (1 + t ^ 2) := by
  rw [circleLift_forward_cancellation]
  have hden : 0 ≤ 1 + t ^ 2 := by positivity
  have hprod : 0 ≤ 4 * amplitude * t := by positivity
  rw [show -4 * amplitude * t = -(4 * amplitude * t) by ring,
    abs_div, abs_neg, abs_of_nonneg hprod, abs_of_nonneg hden]

end

end BoundaryOfSelf.IntrinsicNonradialShearCircleAsymptotic
