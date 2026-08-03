import IntrinsicNonradialShearStereographicDiamondLift

open Set Real Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearStereographicMetricTransport

noncomputable section

open IntrinsicNonradialShearExactSupport
open StandardHausdorffMetricBridge
open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearRationalParameterRefinement
open IntrinsicNonradialShearStereographicDiamondLift

/-! ## IF-BS-22F-F8C31C: metric transport of the rational parameter grid -/

/-- Sup metric on the two active parameters of one stereographic chart. -/
def stereographicParameterGap (t₁ v₁ t₂ v₂ : ℝ) : ℝ :=
  max |t₁ - t₂| |v₁ - v₂|

/-- The explicit ambient radius obtained from the parameter mesh. -/
def exactDiamondMeshRadius (level : ℕ) : ℝ :=
  10 * parameterMeshRadius level

/-- A rational parameter node lifted to the exact directional diamond. -/
def liftedRationalNode {level : ℕ}
    (node : RationalParameterNode level) : BlowUpPoint :=
  stereographicDiamondLift node.hemisphere node.t node.v

/-- The finite lifted grid at refinement level `level`. -/
noncomputable def liftedRationalGrid (level : ℕ) : Finset BlowUpPoint := by
  classical
  exact Finset.univ.image
    (fun node : RationalParameterNode level => liftedRationalNode node)

lemma abs_chartSign (hemisphere : Bool) :
    |chartSign hemisphere| = 1 := by
  cases hemisphere <;> simp [chartSign]

lemma stereographicX_sub_identity (t u : ℝ) :
    stereographicX t - stereographicX u =
      2 * (u - t) * (u + t) /
        ((1 + t ^ 2) * (1 + u ^ 2)) := by
  unfold stereographicX
  field_simp [ne_of_gt (stereographic_denominator_pos t),
    ne_of_gt (stereographic_denominator_pos u)]
  ring

lemma stereographicY_sub_identity (t u : ℝ) :
    stereographicY t - stereographicY u =
      2 * (t - u) * (1 - t * u) /
        ((1 + t ^ 2) * (1 + u ^ 2)) := by
  unfold stereographicY
  field_simp [ne_of_gt (stereographic_denominator_pos t),
    ne_of_gt (stereographic_denominator_pos u)]
  ring

private lemma denominator_one_le (t u : ℝ) :
    1 ≤ (1 + t ^ 2) * (1 + u ^ 2) := by
  have ht : (1 : ℝ) ≤ 1 + t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hu : (1 : ℝ) ≤ 1 + u ^ 2 := by
    nlinarith [sq_nonneg u]
  simpa using mul_le_mul ht hu (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : 0 ≤ 1 + t ^ 2)

lemma abs_stereographicX_sub_le_four
    {t u : ℝ} (ht : t ∈ Icc (-1) 1) (hu : u ∈ Icc (-1) 1) :
    |stereographicX t - stereographicX u| ≤ 4 * |t - u| := by
  have htAbs : |t| ≤ 1 := abs_le.mpr ht
  have huAbs : |u| ≤ 1 := abs_le.mpr hu
  have hsum : |u + t| ≤ 2 := by
    calc
      |u + t| ≤ |u| + |t| := abs_add_le u t
      _ ≤ 1 + 1 := add_le_add huAbs htAbs
      _ = 2 := by norm_num
  have hnum : |2 * (u - t) * (u + t)| ≤ 4 * |t - u| := by
    calc
      |2 * (u - t) * (u + t)| = 2 * |t - u| * |u + t| := by
        simp [abs_mul, abs_sub_comm]
      _ ≤ 2 * |t - u| * 2 :=
        mul_le_mul_of_nonneg_left hsum
          (mul_nonneg (by norm_num) (abs_nonneg _))
      _ = 4 * |t - u| := by ring
  have hdenPos : 0 < (1 + t ^ 2) * (1 + u ^ 2) := by
    positivity
  have hden := denominator_one_le t u
  rw [stereographicX_sub_identity, abs_div, abs_of_pos hdenPos]
  apply (div_le_iff₀ hdenPos).2
  calc
    |2 * (u - t) * (u + t)| ≤ 4 * |t - u| := hnum
    _ ≤ (4 * |t - u|) * ((1 + t ^ 2) * (1 + u ^ 2)) :=
      le_mul_of_one_le_right
        (mul_nonneg (by norm_num) (abs_nonneg _)) hden

lemma abs_stereographicY_sub_le_four
    {t u : ℝ} (ht : t ∈ Icc (-1) 1) (hu : u ∈ Icc (-1) 1) :
    |stereographicY t - stereographicY u| ≤ 4 * |t - u| := by
  have htAbs : |t| ≤ 1 := abs_le.mpr ht
  have huAbs : |u| ≤ 1 := abs_le.mpr hu
  have hproduct : |t| * |u| ≤ 1 := by
    simpa using mul_le_mul htAbs huAbs (abs_nonneg u)
      (by norm_num : (0 : ℝ) ≤ 1)
  have hfactor : |1 - t * u| ≤ 2 := by
    calc
      |1 - t * u| = |(1 : ℝ) + -(t * u)| := by rw [sub_eq_add_neg]
      _ ≤ |(1 : ℝ)| + |-(t * u)| := abs_add_le _ _
      _ = 1 + |t| * |u| := by simp [abs_mul]
      _ ≤ 2 := by linarith
  have hnum : |2 * (t - u) * (1 - t * u)| ≤ 4 * |t - u| := by
    calc
      |2 * (t - u) * (1 - t * u)| =
          2 * |t - u| * |1 - t * u| := by simp [abs_mul]
      _ ≤ 2 * |t - u| * 2 :=
        mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg (by norm_num) (abs_nonneg _))
      _ = 4 * |t - u| := by ring
  have hdenPos : 0 < (1 + t ^ 2) * (1 + u ^ 2) := by
    positivity
  have hden := denominator_one_le t u
  rw [stereographicY_sub_identity, abs_div, abs_of_pos hdenPos]
  apply (div_le_iff₀ hdenPos).2
  calc
    |2 * (t - u) * (1 - t * u)| ≤ 4 * |t - u| := hnum
    _ ≤ (4 * |t - u|) * ((1 + t ^ 2) * (1 + u ^ 2)) :=
      le_mul_of_one_le_right
        (mul_nonneg (by norm_num) (abs_nonneg _)) hden

lemma ambientPlane_dist_le_coordinateAbsSum
    (first second : AmbientPlane) :
    dist first second ≤
      |first.ofLp 0 - second.ofLp 0| +
        |first.ofLp 1 - second.ofLp 1| := by
  have hsq := dist_sq_eq_coordinate_sq_sum first second
  have hsquare :
      dist first second ^ 2 ≤
        (|first.ofLp 0 - second.ofLp 0| +
          |first.ofLp 1 - second.ofLp 1|) ^ 2 := by
    rw [hsq]
    nlinarith [sq_abs (first.ofLp 0 - second.ofLp 0),
      sq_abs (first.ofLp 1 - second.ofLp 1),
      mul_nonneg (abs_nonneg (first.ofLp 0 - second.ofLp 0))
        (abs_nonneg (first.ofLp 1 - second.ofLp 1))]
  have hdist : 0 ≤ dist first second := dist_nonneg
  have hsum : 0 ≤
      |first.ofLp 0 - second.ofLp 0| +
        |first.ofLp 1 - second.ofLp 1| := by positivity
  nlinarith

lemma stereographicDirection_dist_le_eight
    (hemisphere : Bool) {t u : ℝ}
    (ht : t ∈ Icc (-1) 1) (hu : u ∈ Icc (-1) 1) :
    dist (stereographicDirection hemisphere t)
      (stereographicDirection hemisphere u) ≤ 8 * |t - u| := by
  have hx :
      |(stereographicDirection hemisphere t).ofLp 0 -
          (stereographicDirection hemisphere u).ofLp 0| =
        |stereographicX t - stereographicX u| := by
    rw [stereographicDirection_zero, stereographicDirection_zero,
      ← mul_sub, abs_mul, abs_chartSign, one_mul]
  have hy :
      |(stereographicDirection hemisphere t).ofLp 1 -
          (stereographicDirection hemisphere u).ofLp 1| =
        |stereographicY t - stereographicY u| := by
    rw [stereographicDirection_one, stereographicDirection_one]
  calc
    dist (stereographicDirection hemisphere t)
        (stereographicDirection hemisphere u) ≤
      |(stereographicDirection hemisphere t).ofLp 0 -
          (stereographicDirection hemisphere u).ofLp 0| +
        |(stereographicDirection hemisphere t).ofLp 1 -
          (stereographicDirection hemisphere u).ofLp 1| :=
      ambientPlane_dist_le_coordinateAbsSum _ _
    _ = |stereographicX t - stereographicX u| +
        |stereographicY t - stereographicY u| := by rw [hx, hy]
    _ ≤ 8 * |t - u| := by
      nlinarith [abs_stereographicX_sub_le_four ht hu,
        abs_stereographicY_sub_le_four ht hu]

lemma stereographicWidth_sub_le_eight
    (hemisphere : Bool) {t u : ℝ}
    (ht : t ∈ Icc (-1) 1) (hu : u ∈ Icc (-1) 1) :
    |stereographicWidth hemisphere t -
        stereographicWidth hemisphere u| ≤ 8 * |t - u| := by
  have hx := abs_stereographicX_sub_le_four ht hu
  have hy := abs_stereographicY_sub_le_four ht hu
  unfold stereographicWidth
  rw [stereographicDirection_zero, stereographicDirection_zero,
    stereographicDirection_one, stereographicDirection_one]
  have hsign :
      ∀ q : ℝ, |chartSign hemisphere * q| = |q| := by
    intro q
    rw [abs_mul, abs_chartSign, one_mul]
  rw [hsign, hsign]
  calc
    |(|stereographicX t| + |stereographicY t|) -
        (|stereographicX u| + |stereographicY u|)| =
      |(|stereographicX t| - |stereographicX u|) +
        (|stereographicY t| - |stereographicY u|)| := by ring
    _ ≤ abs (|stereographicX t| - |stereographicX u|) +
        abs (|stereographicY t| - |stereographicY u|) := abs_add_le _ _
    _ ≤ |stereographicX t - stereographicX u| +
        |stereographicY t - stereographicY u| :=
      add_le_add (abs_abs_sub_abs_le_abs_sub _ _)
        (abs_abs_sub_abs_le_abs_sub _ _)
    _ ≤ 8 * |t - u| := by nlinarith

private lemma sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  nlinarith [Real.sqrt_nonneg 2,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

lemma stereographicSlope_sub_le_ten
    (hemisphere : Bool) {t₁ t₂ v₁ v₂ : ℝ}
    (ht₁ : t₁ ∈ Icc (-1) 1) (ht₂ : t₂ ∈ Icc (-1) 1)
    (_hv₁ : v₁ ∈ Icc (-1) 1) (hv₂ : v₂ ∈ Icc (-1) 1) :
    |v₁ * stereographicWidth hemisphere t₁ -
        v₂ * stereographicWidth hemisphere t₂| ≤
      10 * stereographicParameterGap t₁ v₁ t₂ v₂ := by
  have hv₂Abs : |v₂| ≤ 1 := abs_le.mpr hv₂
  have hw₁ : stereographicWidth hemisphere t₁ ≤ 2 :=
    le_trans (stereographicWidth_le_sqrt_two hemisphere t₁) sqrt_two_le_two
  have hw₁nonneg : 0 ≤ stereographicWidth hemisphere t₁ :=
    (stereographicWidth_pos hemisphere t₁).le
  have hwidth := stereographicWidth_sub_le_eight hemisphere ht₁ ht₂
  have hfirst :
      |v₁ - v₂| * stereographicWidth hemisphere t₁ ≤
        2 * |v₁ - v₂| := by
    nlinarith [mul_le_mul_of_nonneg_left hw₁ (abs_nonneg (v₁ - v₂))]
  have hsecond :
      |v₂| * |stereographicWidth hemisphere t₁ -
          stereographicWidth hemisphere t₂| ≤ 8 * |t₁ - t₂| := by
    calc
      |v₂| * |stereographicWidth hemisphere t₁ -
          stereographicWidth hemisphere t₂| ≤ |v₂| * (8 * |t₁ - t₂|) :=
        mul_le_mul_of_nonneg_left hwidth (abs_nonneg v₂)
      _ ≤ 1 * (8 * |t₁ - t₂|) :=
        mul_le_mul_of_nonneg_right hv₂Abs (by positivity)
      _ = 8 * |t₁ - t₂| := by ring
  have hgapT : |t₁ - t₂| ≤ stereographicParameterGap t₁ v₁ t₂ v₂ :=
    le_max_left _ _
  have hgapV : |v₁ - v₂| ≤ stereographicParameterGap t₁ v₁ t₂ v₂ :=
    le_max_right _ _
  rw [show v₁ * stereographicWidth hemisphere t₁ -
      v₂ * stereographicWidth hemisphere t₂ =
      (v₁ - v₂) * stereographicWidth hemisphere t₁ +
        v₂ * (stereographicWidth hemisphere t₁ -
          stereographicWidth hemisphere t₂) by ring]
  calc
    |(v₁ - v₂) * stereographicWidth hemisphere t₁ +
        v₂ * (stereographicWidth hemisphere t₁ -
          stereographicWidth hemisphere t₂)| ≤
      |(v₁ - v₂) * stereographicWidth hemisphere t₁| +
        |v₂ * (stereographicWidth hemisphere t₁ -
          stereographicWidth hemisphere t₂)| := abs_add_le _ _
    _ = |v₁ - v₂| * stereographicWidth hemisphere t₁ +
        |v₂| * |stereographicWidth hemisphere t₁ -
          stereographicWidth hemisphere t₂| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hw₁nonneg]
    _ ≤ 2 * |v₁ - v₂| + 8 * |t₁ - t₂| := add_le_add hfirst hsecond
    _ ≤ 10 * stereographicParameterGap t₁ v₁ t₂ v₂ := by nlinarith

/-- On each chart, the full lift is explicitly `10`-Lipschitz in the sup metric. -/
theorem stereographicDiamondLift_dist_le_ten
    (hemisphere : Bool) {t₁ t₂ v₁ v₂ : ℝ}
    (ht₁ : t₁ ∈ Icc (-1) 1) (ht₂ : t₂ ∈ Icc (-1) 1)
    (hv₁ : v₁ ∈ Icc (-1) 1) (hv₂ : v₂ ∈ Icc (-1) 1) :
    dist (stereographicDiamondLift hemisphere t₁ v₁)
      (stereographicDiamondLift hemisphere t₂ v₂) ≤
        10 * stereographicParameterGap t₁ v₁ t₂ v₂ := by
  rw [Prod.dist_eq]
  apply max_le
  · change dist (stereographicDirection hemisphere t₁)
      (stereographicDirection hemisphere t₂) ≤
        10 * stereographicParameterGap t₁ v₁ t₂ v₂
    have hdirection := stereographicDirection_dist_le_eight hemisphere ht₁ ht₂
    have hgapT : |t₁ - t₂| ≤ stereographicParameterGap t₁ v₁ t₂ v₂ :=
      le_max_left _ _
    have hgap0 : 0 ≤ stereographicParameterGap t₁ v₁ t₂ v₂ :=
      le_trans (abs_nonneg (t₁ - t₂)) hgapT
    calc
      dist (stereographicDirection hemisphere t₁)
          (stereographicDirection hemisphere t₂) ≤ 8 * |t₁ - t₂| := hdirection
      _ ≤ 8 * stereographicParameterGap t₁ v₁ t₂ v₂ :=
        mul_le_mul_of_nonneg_left hgapT (by norm_num)
      _ ≤ 10 * stereographicParameterGap t₁ v₁ t₂ v₂ := by nlinarith
  · rw [Real.dist_eq]
    exact stereographicSlope_sub_le_ten hemisphere ht₁ ht₂ hv₁ hv₂

theorem liftedRationalNode_mem_exactDiamond
    {level : ℕ} (node : RationalParameterNode level) :
    liftedRationalNode node ∈ directionalDiamondBand := by
  obtain ⟨_, hv⟩ := parameterNode_coordinates_mem node
  exact stereographicDiamondLift_mem node.hemisphere node.t hv

/-- Every exact diamond point is within the explicit transported mesh radius. -/
theorem exists_liftedRationalNode_close
    (level : ℕ) (point : BlowUpPoint)
    (hpoint : point ∈ directionalDiamondBand) :
    ∃ node : RationalParameterNode level,
      dist point (liftedRationalNode node) ≤ exactDiamondMeshRadius level := by
  obtain ⟨hemisphere, t, v, ht, hv, hlift⟩ :=
    two_stereographic_charts_surjective point hpoint
  obtain ⟨node, hhemisphere, hclose⟩ :=
    exists_parameterNode_close level hemisphere ht hv
  obtain ⟨hnodeT, hnodeV⟩ := parameterNode_coordinates_mem node
  refine ⟨node, ?_⟩
  calc
    dist point (liftedRationalNode node) =
        dist (stereographicDiamondLift hemisphere t v)
          (stereographicDiamondLift hemisphere node.t node.v) := by
      rw [hlift]
      simp [liftedRationalNode, hhemisphere]
    _ ≤ 10 * stereographicParameterGap t v node.t node.v :=
      stereographicDiamondLift_dist_le_ten hemisphere ht hnodeT hv hnodeV
    _ = 10 * parameterDistance t v node := by
      rfl
    _ ≤ 10 * parameterMeshRadius level :=
      mul_le_mul_of_nonneg_left hclose (by norm_num)
    _ = exactDiamondMeshRadius level := rfl

/-- The lifted grid is finite, lies in the exact diamond, and covers it. -/
theorem liftedRationalGrid_is_deltaNet (level : ℕ) :
    (∀ gridPoint ∈ liftedRationalGrid level,
      gridPoint ∈ directionalDiamondBand) ∧
    (∀ point ∈ directionalDiamondBand,
      ∃ gridPoint ∈ liftedRationalGrid level,
        dist point gridPoint ≤ exactDiamondMeshRadius level) := by
  classical
  constructor
  · intro gridPoint hgrid
    rw [liftedRationalGrid, Finset.mem_image] at hgrid
    obtain ⟨node, _, rfl⟩ := hgrid
    exact liftedRationalNode_mem_exactDiamond node
  · intro point hpoint
    obtain ⟨node, hclose⟩ := exists_liftedRationalNode_close level point hpoint
    refine ⟨liftedRationalNode node, ?_, hclose⟩
    exact Finset.mem_image.mpr ⟨node, Finset.mem_univ node, rfl⟩

theorem exactDiamondMeshRadius_eq (level : ℕ) :
    exactDiamondMeshRadius level = 20 / (level + 1 : ℝ) := by
  unfold exactDiamondMeshRadius parameterMeshRadius
  ring

theorem exactDiamondMeshRadius_tendsto_zero :
    Tendsto exactDiamondMeshRadius atTop (nhds 0) := by
  have h := parameterMeshRadius_tendsto_zero.const_mul 10
  change Tendsto (fun level => 10 * parameterMeshRadius level) atTop (nhds 0)
  simpa using h

end

end BoundaryOfSelf.IntrinsicNonradialShearStereographicMetricTransport
