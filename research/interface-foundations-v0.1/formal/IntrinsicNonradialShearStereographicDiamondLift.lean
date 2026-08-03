import IntrinsicNonradialShearRationalParameterRefinement

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearStereographicDiamondLift

noncomputable section

open StandardHausdorffMetricBridge
open LocalSegmentRealCompletion
open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearExactSupport
open IntrinsicNonradialShearKernelSharp
open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearDiagonalBlowUpInverse
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearRealizableClosure
open IntrinsicNonradialShearRealizableCertificate
open IntrinsicNonradialShearRationalParameterRefinement

/-! ## IF-BS-22F-F8C31B: two-chart lift onto the exact directional diamond -/

def chartSign (hemisphere : Bool) : ℝ :=
  if hemisphere then 1 else -1

def stereographicX (t : ℝ) : ℝ :=
  (1 - t ^ 2) / (1 + t ^ 2)

def stereographicY (t : ℝ) : ℝ :=
  2 * t / (1 + t ^ 2)

def stereographicDirection (hemisphere : Bool) (t : ℝ) : AmbientPlane :=
  planeEmbedding
    ({ x := chartSign hemisphere * stereographicX t
       y := stereographicY t } : RealPlanePoint)

def stereographicWidth (hemisphere : Bool) (t : ℝ) : ℝ :=
  |(stereographicDirection hemisphere t).ofLp 0| +
    |(stereographicDirection hemisphere t).ofLp 1|

def stereographicDiamondLift
    (hemisphere : Bool) (t v : ℝ) : BlowUpPoint :=
  (stereographicDirection hemisphere t,
    v * stereographicWidth hemisphere t)

lemma chartSign_sq (hemisphere : Bool) :
    chartSign hemisphere ^ 2 = 1 := by
  cases hemisphere <;> simp [chartSign]

lemma stereographic_denominator_pos (t : ℝ) :
    0 < 1 + t ^ 2 := by
  positivity

@[simp] lemma stereographicDirection_zero
    (hemisphere : Bool) (t : ℝ) :
    (stereographicDirection hemisphere t).ofLp 0 =
      chartSign hemisphere * stereographicX t := by
  simp [stereographicDirection, planeEmbedding]

@[simp] lemma stereographicDirection_one
    (hemisphere : Bool) (t : ℝ) :
    (stereographicDirection hemisphere t).ofLp 1 =
      stereographicY t := by
  simp [stereographicDirection, planeEmbedding]

theorem stereographicDirection_coordinate_unit
    (hemisphere : Bool) (t : ℝ) :
    (stereographicDirection hemisphere t).ofLp 0 ^ 2 +
      (stereographicDirection hemisphere t).ofLp 1 ^ 2 = 1 := by
  rw [stereographicDirection_zero, stereographicDirection_one]
  rw [mul_pow, chartSign_sq, one_mul]
  unfold stereographicX stereographicY
  field_simp [ne_of_gt (stereographic_denominator_pos t)]
  ring

theorem stereographicDirection_mem_sphere
    (hemisphere : Bool) (t : ℝ) :
    stereographicDirection hemisphere t ∈
      Metric.sphere kernelOrigin 1 := by
  rw [Metric.mem_sphere, dist_comm]
  have hunit := stereographicDirection_coordinate_unit hemisphere t
  have hsq :
      dist kernelOrigin (stereographicDirection hemisphere t) ^ 2 = 1 := by
    rw [dist_sq_eq_coordinate_sq_sum]
    simpa [kernelOrigin, planeEmbedding] using hunit
  have hnonnegative :
      0 ≤ dist kernelOrigin (stereographicDirection hemisphere t) :=
    dist_nonneg
  nlinarith

lemma stereographicWidth_pos
    (hemisphere : Bool) (t : ℝ) :
    0 < stereographicWidth hemisphere t := by
  simpa [stereographicWidth, directionWidth] using
    directionWidth_pos
      (stereographicDirection_coordinate_unit hemisphere t)

lemma unit_directionWidth_le_sqrt_two
    {direction : AmbientPlane}
    (hunit :
      direction.ofLp 0 ^ 2 + direction.ofLp 1 ^ 2 = 1) :
    directionWidth direction ≤ Real.sqrt 2 := by
  have hwidth0 : 0 ≤ directionWidth direction :=
    (directionWidth_pos hunit).le
  have hsq : directionWidth direction ^ 2 ≤ 2 := by
    unfold directionWidth
    nlinarith [sq_nonneg
      (|direction.ofLp 0| - |direction.ofLp 1|),
      sq_abs (direction.ofLp 0), sq_abs (direction.ofLp 1)]
  nlinarith [sqrt_two_nonneg, sqrt_two_sq]

lemma stereographicWidth_le_sqrt_two
    (hemisphere : Bool) (t : ℝ) :
    stereographicWidth hemisphere t ≤ Real.sqrt 2 := by
  simpa [stereographicWidth, directionWidth] using
    unit_directionWidth_le_sqrt_two
      (stereographicDirection_coordinate_unit hemisphere t)

theorem stereographicDiamondLift_mem
    (hemisphere : Bool) (t : ℝ)
    {v : ℝ} (hv : v ∈ Set.Icc (-1 : ℝ) 1) :
    stereographicDiamondLift hemisphere t v ∈
      directionalDiamondBand := by
  have hvabs : |v| ≤ 1 := abs_le.mpr hv
  have hwidth0 : 0 ≤ stereographicWidth hemisphere t :=
    (stereographicWidth_pos hemisphere t).le
  have hslope :
      |v * stereographicWidth hemisphere t| ≤
        stereographicWidth hemisphere t := by
    rw [abs_mul, abs_of_nonneg hwidth0]
    nlinarith [abs_nonneg v]
  rw [directionalDiamondBand, directionalBlowUpChamber]
  refine ⟨⟨stereographicDirection_mem_sphere hemisphere t, ?_⟩, ?_⟩
  · change v * stereographicWidth hemisphere t ∈
      Set.Icc (-Real.sqrt 2) (Real.sqrt 2)
    exact abs_le.mp
      (hslope.trans (stereographicWidth_le_sqrt_two hemisphere t))
  · change |v * stereographicWidth hemisphere t| ≤
      |(stereographicDirection hemisphere t).ofLp 0| +
        |(stereographicDirection hemisphere t).ofLp 1|
    simpa [stereographicWidth] using hslope

lemma eastParameter_mem_Icc
    {x y : ℝ}
    (hunit : x ^ 2 + y ^ 2 = 1)
    (hx : 0 ≤ x) :
    y / (1 + x) ∈ Set.Icc (-1 : ℝ) 1 := by
  have hden : 0 < 1 + x := by linarith
  have hsq : |y| ^ 2 ≤ (1 + x) ^ 2 := by
    rw [sq_abs]
    nlinarith
  have habs : |y| ≤ 1 + x :=
    (sq_le_sq₀ (abs_nonneg y) (le_of_lt hden)).mp hsq
  apply abs_le.mp
  rw [abs_div, abs_of_pos hden]
  exact (div_le_one hden).2 habs

lemma westParameter_mem_Icc
    {x y : ℝ}
    (hunit : x ^ 2 + y ^ 2 = 1)
    (hx : x ≤ 0) :
    y / (1 - x) ∈ Set.Icc (-1 : ℝ) 1 := by
  have hden : 0 < 1 - x := by linarith
  have hsq : |y| ^ 2 ≤ (1 - x) ^ 2 := by
    rw [sq_abs]
    nlinarith
  have habs : |y| ≤ 1 - x :=
    (sq_le_sq₀ (abs_nonneg y) (le_of_lt hden)).mp hsq
  apply abs_le.mp
  rw [abs_div, abs_of_pos hden]
  exact (div_le_one hden).2 habs

lemma east_stereographicX
    {x y : ℝ}
    (hunit : x ^ 2 + y ^ 2 = 1)
    (hx : 0 ≤ x) :
    stereographicX (y / (1 + x)) = x := by
  have hden : 0 < 1 + x := by linarith
  have hsum : (1 + x) ^ 2 + y ^ 2 = 2 * (1 + x) := by
    nlinarith
  have hdiff : (1 + x) ^ 2 - y ^ 2 = 2 * x * (1 + x) := by
    nlinarith
  have hsumPos : 0 < (1 + x) ^ 2 + y ^ 2 := by
    rw [hsum]
    positivity
  calc
    stereographicX (y / (1 + x)) =
        ((1 + x) ^ 2 - y ^ 2) /
          ((1 + x) ^ 2 + y ^ 2) := by
      unfold stereographicX
      field_simp [ne_of_gt hden, ne_of_gt hsumPos]
    _ = (2 * x * (1 + x)) / (2 * (1 + x)) := by
      rw [hdiff, hsum]
    _ = x := by
      field_simp [ne_of_gt hden]

lemma east_stereographicY
    {x y : ℝ}
    (hunit : x ^ 2 + y ^ 2 = 1)
    (hx : 0 ≤ x) :
    stereographicY (y / (1 + x)) = y := by
  have hden : 0 < 1 + x := by linarith
  have hsum : (1 + x) ^ 2 + y ^ 2 = 2 * (1 + x) := by
    nlinarith
  have hsumPos : 0 < (1 + x) ^ 2 + y ^ 2 := by
    rw [hsum]
    positivity
  calc
    stereographicY (y / (1 + x)) =
        (2 * y * (1 + x)) /
          ((1 + x) ^ 2 + y ^ 2) := by
      unfold stereographicY
      field_simp [ne_of_gt hden, ne_of_gt hsumPos]
    _ = (2 * y * (1 + x)) / (2 * (1 + x)) := by
      rw [hsum]
    _ = y := by
      field_simp [ne_of_gt hden]

lemma west_stereographicX
    {x y : ℝ}
    (hunit : x ^ 2 + y ^ 2 = 1)
    (hx : x ≤ 0) :
    stereographicX (y / (1 - x)) = -x := by
  have hden : 0 < 1 - x := by linarith
  have hsum : (1 - x) ^ 2 + y ^ 2 = 2 * (1 - x) := by
    nlinarith
  have hdiff : (1 - x) ^ 2 - y ^ 2 = -2 * x * (1 - x) := by
    nlinarith
  have hsumPos : 0 < (1 - x) ^ 2 + y ^ 2 := by
    rw [hsum]
    positivity
  calc
    stereographicX (y / (1 - x)) =
        ((1 - x) ^ 2 - y ^ 2) /
          ((1 - x) ^ 2 + y ^ 2) := by
      unfold stereographicX
      field_simp [ne_of_gt hden, ne_of_gt hsumPos]
    _ = (-2 * x * (1 - x)) / (2 * (1 - x)) := by
      rw [hdiff, hsum]
    _ = -x := by
      field_simp [ne_of_gt hden]

lemma west_stereographicY
    {x y : ℝ}
    (hunit : x ^ 2 + y ^ 2 = 1)
    (hx : x ≤ 0) :
    stereographicY (y / (1 - x)) = y := by
  have hden : 0 < 1 - x := by linarith
  have hsum : (1 - x) ^ 2 + y ^ 2 = 2 * (1 - x) := by
    nlinarith
  have hsumPos : 0 < (1 - x) ^ 2 + y ^ 2 := by
    rw [hsum]
    positivity
  calc
    stereographicY (y / (1 - x)) =
        (2 * y * (1 - x)) /
          ((1 - x) ^ 2 + y ^ 2) := by
      unfold stereographicY
      field_simp [ne_of_gt hden, ne_of_gt hsumPos]
    _ = (2 * y * (1 - x)) / (2 * (1 - x)) := by
      rw [hsum]
    _ = y := by
      field_simp [ne_of_gt hden]

theorem two_stereographic_charts_surjective :
    ∀ point ∈ directionalDiamondBand,
      ∃ hemisphere : Bool, ∃ t v : ℝ,
        t ∈ Set.Icc (-1 : ℝ) 1 ∧
        v ∈ Set.Icc (-1 : ℝ) 1 ∧
        stereographicDiamondLift hemisphere t v = point := by
  intro point hpoint
  rcases diamond_unit_and_slope hpoint with ⟨hunit, hslope⟩
  let x : ℝ := point.1.ofLp 0
  let y : ℝ := point.1.ofLp 1
  let width : ℝ := directionWidth point.1
  let v : ℝ := point.2 / width
  have hxy : x ^ 2 + y ^ 2 = 1 := by
    simpa [x, y] using hunit
  have hwidthPos : 0 < width := by
    simpa [width] using directionWidth_pos hunit
  have hslopeWidth : |point.2| ≤ width := by
    simpa [width, directionWidth] using hslope
  have hv : v ∈ Set.Icc (-1 : ℝ) 1 := by
    apply abs_le.mp
    dsimp [v]
    rw [abs_div, abs_of_pos hwidthPos]
    exact (div_le_one hwidthPos).2 hslopeWidth
  by_cases hx : 0 ≤ x
  · let t : ℝ := y / (1 + x)
    have ht : t ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [t] using eastParameter_mem_Icc hxy hx
    have hxchart : stereographicX t = x := by
      simpa [t] using east_stereographicX hxy hx
    have hychart : stereographicY t = y := by
      simpa [t] using east_stereographicY hxy hx
    have hdir : stereographicDirection true t = point.1 := by
      ext index
      fin_cases index <;>
        simp [stereographicDirection, chartSign, planeEmbedding,
          x, y, hxchart, hychart]
    have hwidth :
        stereographicWidth true t = width := by
      unfold stereographicWidth width directionWidth
      rw [hdir]
    refine ⟨true, t, v, ht, hv, ?_⟩
    apply Prod.ext
    · exact hdir
    · change v * stereographicWidth true t = point.2
      rw [hwidth]
      dsimp [v]
      field_simp [hwidthPos.ne']
  · have hx' : x ≤ 0 := le_of_not_ge hx
    let t : ℝ := y / (1 - x)
    have ht : t ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [t] using westParameter_mem_Icc hxy hx'
    have hxchart : stereographicX t = -x := by
      simpa [t] using west_stereographicX hxy hx'
    have hychart : stereographicY t = y := by
      simpa [t] using west_stereographicY hxy hx'
    have hdir : stereographicDirection false t = point.1 := by
      ext index
      fin_cases index <;>
        simp [stereographicDirection, chartSign, planeEmbedding,
          x, y, hxchart, hychart]
    have hwidth :
        stereographicWidth false t = width := by
      unfold stereographicWidth width directionWidth
      rw [hdir]
    refine ⟨false, t, v, ht, hv, ?_⟩
    apply Prod.ext
    · exact hdir
    · change v * stereographicWidth false t = point.2
      rw [hwidth]
      dsimp [v]
      field_simp [hwidthPos.ne']

end

end BoundaryOfSelf.IntrinsicNonradialShearStereographicDiamondLift
