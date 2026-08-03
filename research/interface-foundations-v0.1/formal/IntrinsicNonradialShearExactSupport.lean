import IntrinsicNonradialShearLimit

open Set Filter Metric Topology
open scoped ENNReal

namespace BoundaryOfSelf.IntrinsicNonradialShearExactSupport

open BoundaryOfSelf.StandardHausdorffMetricBridge
open BoundaryOfSelf.IntrinsicNonradialShearLimit
open BoundaryOfSelf.CompactTentHomeomorphism
open BoundaryOfSelf.LocalSegmentRealCompletion
open BoundaryOfSelf.OneSidedEuclideanContourBound

/-- Coordinate homeomorphism between the Euclidean plane and an ordinary pair. -/
def pairPlaneHomeomorph : (ℝ × ℝ) ≃ₜ AmbientPlane where
  toFun pair := WithLp.toLp 2 ![pair.1, pair.2]
  invFun point := (point.ofLp 0, point.ofLp 1)
  left_inv pair := by ext <;> simp
  right_inv point := by
    ext i
    fin_cases i <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The open square in which a nonzero intrinsic shear actually moves points. -/
def openShearSquare : Set (ℝ × ℝ) := Ioo (-1) 1 ×ˢ Ioo (-1) 1

/-- The minimal closed square containing every actually moved point. -/
def closedShearSquare : Set (ℝ × ℝ) := Icc (-1) 1 ×ˢ Icc (-1) 1

/-- Exact open support, expressed in the existing ambient plane. -/
def intrinsicShearOpenSupport : Set AmbientPlane :=
  pairPlaneHomeomorph.symm ⁻¹' openShearSquare

/-- Exact closed carrier: the closure of the actual moving set. -/
def intrinsicShearExactCarrier : Set AmbientPlane :=
  pairPlaneHomeomorph.symm ⁻¹' closedShearSquare

/-- The four-edge perimeter of the exact square carrier. -/
def intrinsicShearSquarePerimeter : Set AmbientPlane :=
  pairPlaneHomeomorph.symm ⁻¹'
    ((Icc (-1) 1 ×ˢ ({-1, 1} : Set ℝ)) ∪
      (({-1, 1} : Set ℝ) ×ˢ Icc (-1) 1))

/-- The set of points actually changed by one shear amplitude. -/
def intrinsicShearMovingSet (amplitude : ℝ) : Set AmbientPlane :=
  {point | intrinsicShearMap amplitude point ≠ point}

lemma tentBump_pos_iff_abs_lt_one (x : ℝ) :
    0 < tentBump x ↔ |x| < 1 := by
  simp [tentBump]

lemma tentBump_ne_zero_iff_abs_lt_one (x : ℝ) :
    tentBump x ≠ 0 ↔ |x| < 1 := by
  rw [ne_eq, ← not_iff_not]
  simp [tentBump]

lemma intrinsicShearMap_eq_self_iff (amplitude : ℝ) (point : AmbientPlane) :
    intrinsicShearMap amplitude point = point ↔
      amplitude * shearKernel point = 0 := by
  constructor
  · intro h
    have hCoord := congrArg (fun p : AmbientPlane => p.ofLp 1) h
    simpa [intrinsicShearMap, planeEmbedding] using hCoord
  · intro h
    ext i
    fin_cases i
    · simp [intrinsicShearMap, planeEmbedding]
    · simp [intrinsicShearMap, planeEmbedding, h]

lemma mem_intrinsicShearOpenSupport_iff (point : AmbientPlane) :
    point ∈ intrinsicShearOpenSupport ↔
      |point.ofLp 0| < 1 ∧ |point.ofLp 1| < 1 := by
  simp [intrinsicShearOpenSupport, openShearSquare, pairPlaneHomeomorph, abs_lt]

lemma mem_intrinsicShearExactCarrier_iff (point : AmbientPlane) :
    point ∈ intrinsicShearExactCarrier ↔
      |point.ofLp 0| ≤ 1 ∧ |point.ofLp 1| ≤ 1 := by
  dsimp [intrinsicShearExactCarrier, closedShearSquare, pairPlaneHomeomorph]
  change
    ((point.ofLp 0 ∈ Icc (-1) 1) ∧ (point.ofLp 1 ∈ Icc (-1) 1)) ↔
      |point.ofLp 0| ≤ 1 ∧ |point.ofLp 1| ≤ 1
  simp [abs_le]

/-- For every positive amplitude, movement occurs at exactly the open square. -/
theorem intrinsicShearMovingSet_eq_openSupport
    (amplitude : ℝ) (hAmplitude : 0 < amplitude) :
    intrinsicShearMovingSet amplitude = intrinsicShearOpenSupport := by
  ext point
  rw [mem_intrinsicShearOpenSupport_iff]
  simp only [intrinsicShearMovingSet, mem_setOf_eq]
  rw [Ne, intrinsicShearMap_eq_self_iff]
  simp [shearKernel, hAmplitude.ne', tentBump_ne_zero_iff_abs_lt_one]

/-- The exact carrier is literally the closure of the actually moved points. -/
theorem closure_intrinsicShearOpenSupport :
    closure intrinsicShearOpenSupport = intrinsicShearExactCarrier := by
  unfold intrinsicShearOpenSupport intrinsicShearExactCarrier
  rw [← pairPlaneHomeomorph.symm.preimage_closure]
  congr 1
  unfold openShearSquare closedShearSquare
  rw [closure_prod_eq,
    closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]

theorem closure_intrinsicShearMovingSet
    (amplitude : ℝ) (hAmplitude : 0 < amplitude) :
    closure (intrinsicShearMovingSet amplitude) = intrinsicShearExactCarrier := by
  rw [intrinsicShearMovingSet_eq_openSupport amplitude hAmplitude,
    closure_intrinsicShearOpenSupport]

/-- Compactness is inherited from the closed coordinate square. -/
theorem intrinsicShearExactCarrier_compact :
    IsCompact intrinsicShearExactCarrier := by
  unfold intrinsicShearExactCarrier
  rw [← pairPlaneHomeomorph.image_eq_preimage_symm]
  exact (isCompact_Icc.prod isCompact_Icc).image pairPlaneHomeomorph.continuous

/-- Exact square-like frontier: no circular over-carrier remains. -/
theorem frontier_intrinsicShearExactCarrier :
    frontier intrinsicShearExactCarrier = intrinsicShearSquarePerimeter := by
  unfold intrinsicShearExactCarrier intrinsicShearSquarePerimeter
  calc
    frontier (pairPlaneHomeomorph.symm ⁻¹' closedShearSquare) =
        pairPlaneHomeomorph.symm ⁻¹' frontier closedShearSquare :=
      (pairPlaneHomeomorph.symm.preimage_frontier closedShearSquare).symm
    _ = pairPlaneHomeomorph.symm ⁻¹'
        ((Icc (-1) 1 ×ˢ ({-1, 1} : Set ℝ)) ∪
          (({-1, 1} : Set ℝ) ×ˢ Icc (-1) 1)) := by
      congr 1
      rw [show closedShearSquare = Icc (-1) 1 ×ˢ Icc (-1) 1 from rfl,
        frontier_prod_eq, frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1),
        ]
      simp only [isClosed_Icc.closure_eq]

/-- Any closed carrier outside which the map is the identity contains the exact carrier. -/
theorem intrinsicShearExactCarrier_minimal
    (amplitude : ℝ) (hAmplitude : 0 < amplitude)
    {carrier : Set AmbientPlane} (hCarrierClosed : _root_.IsClosed carrier)
    (hIdentityOutside : ∀ point, point ∉ carrier →
      intrinsicShearMap amplitude point = point) :
    intrinsicShearExactCarrier ⊆ carrier := by
  rw [← closure_intrinsicShearMovingSet amplitude hAmplitude]
  apply closure_minimal
  · intro point hMoving
    by_contra hOutside
    exact hMoving (hIdentityOutside point hOutside)
  · exact hCarrierClosed

/-- Squared Euclidean distance in the two ambient coordinates. -/
lemma dist_sq_eq_coordinate_sq_sum (first second : AmbientPlane) :
    dist first second ^ 2 =
      (first.ofLp 0 - second.ofLp 0) ^ 2 +
        (first.ofLp 1 - second.ofLp 1) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt]
  · simp [Fin.sum_univ_two]
  · positivity

lemma coordinate_abs_sum_le_sqrt_two_mul_dist (first second : AmbientPlane) :
    |first.ofLp 0 - second.ofLp 0| +
        |first.ofLp 1 - second.ofLp 1| ≤
      Real.sqrt 2 * dist first second := by
  let x := |first.ofLp 0 - second.ofLp 0|
  let y := |first.ofLp 1 - second.ofLp 1|
  have hLeft : 0 ≤ x + y := by positivity
  have hRight : 0 ≤ Real.sqrt 2 * dist first second := by positivity
  apply (sq_le_sq₀ hLeft hRight).mp
  have hAdd := add_sq_le (a := x) (b := y)
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    dist_sq_eq_coordinate_sq_sum]
  simpa [x, y, sq_abs, mul_add] using hAdd

lemma shearKernel_abs_sub_le_coordinate_sum (first second : AmbientPlane) :
    |shearKernel first - shearKernel second| ≤
      |first.ofLp 0 - second.ofLp 0| +
        |first.ofLp 1 - second.ofLp 1| := by
  let fx := tentBump (first.ofLp 0)
  let fy := tentBump (first.ofLp 1)
  let gx := tentBump (second.ofLp 0)
  let gy := tentBump (second.ofLp 1)
  have hfx : 0 ≤ fx := tentBump_nonnegative _
  have hfy : 0 ≤ fy := tentBump_nonnegative _
  have hgx : 0 ≤ gx := tentBump_nonnegative _
  have hgy : 0 ≤ gy := tentBump_nonnegative _
  have hfxOne : fx ≤ 1 := tentBump_le_one _
  have hfyOne : fy ≤ 1 := tentBump_le_one _
  have hgxOne : gx ≤ 1 := tentBump_le_one _
  have hgyOne : gy ≤ 1 := tentBump_le_one _
  have hx : |fx - gx| ≤ |first.ofLp 0 - second.ofLp 0| := by
    simpa [Real.dist_eq] using tentBump_lipschitz.dist_le_mul
      (first.ofLp 0) (second.ofLp 0)
  have hy : |fy - gy| ≤ |first.ofLp 1 - second.ofLp 1| := by
    simpa [Real.dist_eq] using tentBump_lipschitz.dist_le_mul
      (first.ofLp 1) (second.ofLp 1)
  have hFirstTerm : |fx - gx| * |fy| ≤ |first.ofLp 0 - second.ofLp 0| := by
    calc
      |fx - gx| * |fy| = |fx - gx| * fy := by rw [abs_of_nonneg hfy]
      _ ≤ |fx - gx| * 1 := mul_le_mul_of_nonneg_left hfyOne (abs_nonneg _)
      _ ≤ |first.ofLp 0 - second.ofLp 0| * 1 :=
        mul_le_mul_of_nonneg_right hx (by norm_num)
      _ = _ := by ring
  have hSecondTerm : |gx| * |fy - gy| ≤ |first.ofLp 1 - second.ofLp 1| := by
    calc
      |gx| * |fy - gy| = gx * |fy - gy| := by rw [abs_of_nonneg hgx]
      _ ≤ 1 * |fy - gy| := mul_le_mul_of_nonneg_right hgxOne (abs_nonneg _)
      _ ≤ 1 * |first.ofLp 1 - second.ofLp 1| :=
        mul_le_mul_of_nonneg_left hy (by norm_num)
      _ = _ := by ring
  rw [show shearKernel first - shearKernel second =
      (fx - gx) * fy + gx * (fy - gy) by
        simp [shearKernel, fx, fy, gx, gy]
        ring]
  calc
    |(fx - gx) * fy + gx * (fy - gy)| ≤
        |(fx - gx) * fy| + |gx * (fy - gy)| := abs_add_le _ _
    _ = |fx - gx| * |fy| + |gx| * |fy - gy| := by rw [abs_mul, abs_mul]
    _ ≤ _ := add_le_add hFirstTerm hSecondTerm

/-- Improved global kernel coefficient, replacing the earlier safe coefficient `2`. -/
theorem shearKernel_abs_sub_le_sqrt_two (first second : AmbientPlane) :
    |shearKernel first - shearKernel second| ≤
      Real.sqrt 2 * dist first second :=
  (shearKernel_abs_sub_le_coordinate_sum first second).trans
    (coordinate_abs_sum_le_sqrt_two_mul_dist first second)

/-- Improved direct global metric envelope. -/
theorem intrinsicShearMap_dist_le_sqrt_two
    (amplitude : ℝ) (hAmplitude : 0 ≤ amplitude)
    (first second : AmbientPlane) :
    dist (intrinsicShearMap amplitude first) (intrinsicShearMap amplitude second) ≤
      (1 + Real.sqrt 2 * amplitude) * dist first second := by
  rw [intrinsicShearMap_eq_add_displacement,
    intrinsicShearMap_eq_add_displacement]
  calc
    dist (first + verticalDisplacement amplitude first)
        (second + verticalDisplacement amplitude second) ≤
      dist first second +
        dist (verticalDisplacement amplitude first) (verticalDisplacement amplitude second) :=
      dist_add_add_le _ _ _ _
    _ = dist first second + amplitude * |shearKernel first - shearKernel second| := by
      rw [verticalDisplacement_dist, abs_of_nonneg hAmplitude]
    _ ≤ dist first second + amplitude * (Real.sqrt 2 * dist first second) := by
      gcongr
      exact shearKernel_abs_sub_le_sqrt_two first second
    _ = (1 + Real.sqrt 2 * amplitude) * dist first second := by ring

/-- Improved co-Lipschitz envelope; valid before the coefficient reaches zero. -/
theorem intrinsicShearMap_colipschitz_sqrt_two
    (amplitude : ℝ) (hAmplitude : 0 ≤ amplitude)
    (first second : AmbientPlane) :
    (1 - Real.sqrt 2 * amplitude) * dist first second ≤
      dist (intrinsicShearMap amplitude first) (intrinsicShearMap amplitude second) := by
  have hReverse : dist first second ≤
      dist (intrinsicShearMap amplitude first) (intrinsicShearMap amplitude second) +
        dist (verticalDisplacement amplitude first) (verticalDisplacement amplitude second) := by
    rw [intrinsicShearMap_eq_add_displacement,
      intrinsicShearMap_eq_add_displacement]
    simpa [dist_neg_neg] using
      (dist_add_add_le
        (first + verticalDisplacement amplitude first)
        (-verticalDisplacement amplitude first)
        (second + verticalDisplacement amplitude second)
        (-verticalDisplacement amplitude second))
  rw [verticalDisplacement_dist, abs_of_nonneg hAmplitude] at hReverse
  have hDisp : amplitude * |shearKernel first - shearKernel second| ≤
      amplitude * (Real.sqrt 2 * dist first second) := by
    gcongr
    exact shearKernel_abs_sub_le_sqrt_two first second
  nlinarith

lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have hSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hNonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

lemma intrinsicShear_sqrt_two_gap_pos
    (amplitude : ℝ) (hQuarter : amplitude ≤ 1 / 4) :
    0 < 1 - Real.sqrt 2 * amplitude := by
  have hSqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hProduct : Real.sqrt 2 * amplitude < 1 := by
    calc
      Real.sqrt 2 * amplitude ≤ Real.sqrt 2 * (1 / 4) := by gcongr
      _ < 2 * (1 / 4) := by gcongr; exact sqrt_two_lt_two
      _ = 1 / 2 := by norm_num
      _ < 1 := by norm_num
  linarith

/-- Improved inverse estimate derived from the positive `1-sqrt(2)a` gap. -/
theorem intrinsicShearEquiv_inverse_dist_le_sqrt_two
    (amplitude : ℝ) (hAmplitude : 0 ≤ amplitude)
    (hQuarter : amplitude ≤ 1 / 4)
    (first second : AmbientPlane) :
    dist ((intrinsicShearEquiv amplitude hAmplitude hQuarter).symm first)
        ((intrinsicShearEquiv amplitude hAmplitude hQuarter).symm second) ≤
      (1 / (1 - Real.sqrt 2 * amplitude)) * dist first second := by
  let firstPreimage :=
    (intrinsicShearEquiv amplitude hAmplitude hQuarter).symm first
  let secondPreimage :=
    (intrinsicShearEquiv amplitude hAmplitude hQuarter).symm second
  have hCo := intrinsicShearMap_colipschitz_sqrt_two amplitude hAmplitude
    firstPreimage secondPreimage
  have hFirst : intrinsicShearMap amplitude firstPreimage = first := by
    rw [← intrinsicShearEquiv_apply amplitude hAmplitude hQuarter firstPreimage]
    exact (intrinsicShearEquiv amplitude hAmplitude hQuarter).apply_symm_apply first
  have hSecond : intrinsicShearMap amplitude secondPreimage = second := by
    rw [← intrinsicShearEquiv_apply amplitude hAmplitude hQuarter secondPreimage]
    exact (intrinsicShearEquiv amplitude hAmplitude hQuarter).apply_symm_apply second
  rw [hFirst, hSecond] at hCo
  have hGap := intrinsicShear_sqrt_two_gap_pos amplitude hQuarter
  have hDiv : dist firstPreimage secondPreimage ≤
      dist first second / (1 - Real.sqrt 2 * amplitude) :=
    (le_div_iff₀ hGap).2 (by simpa [mul_comm] using hCo)
  simpa [firstPreimage, secondPreimage, div_eq_mul_inv, mul_comm] using hDiv

lemma one_add_sqrt_two_mul_le_inverse_gap
    (amplitude : ℝ) (hQuarter : amplitude ≤ 1 / 4) :
    1 + Real.sqrt 2 * amplitude ≤
      1 / (1 - Real.sqrt 2 * amplitude) := by
  have hGap := intrinsicShear_sqrt_two_gap_pos amplitude hQuarter
  rw [le_div_iff₀ hGap]
  have hSq : 0 ≤ (Real.sqrt 2 * amplitude) ^ 2 := sq_nonneg _
  nlinarith

/-- One common improved constant controls the forward map. -/
theorem intrinsicShearMap_dist_le_inverse_gap
    (amplitude : ℝ) (hAmplitude : 0 ≤ amplitude)
    (hQuarter : amplitude ≤ 1 / 4)
    (first second : AmbientPlane) :
    dist (intrinsicShearMap amplitude first) (intrinsicShearMap amplitude second) ≤
      (1 / (1 - Real.sqrt 2 * amplitude)) * dist first second := by
  exact (intrinsicShearMap_dist_le_sqrt_two amplitude hAmplitude first second).trans
    (mul_le_mul_of_nonneg_right
      (one_add_sqrt_two_mul_le_inverse_gap amplitude hQuarter)
      dist_nonneg)

/-- Vertical-axis probe used to certify optimal one-dimensional slopes. -/
def verticalAxisPoint (y : ℝ) : AmbientPlane :=
  planeEmbedding { x := 0, y := y }

lemma verticalAxisPoint_dist (u v : ℝ) :
    dist (verticalAxisPoint u) (verticalAxisPoint v) = |u - v| := by
  simp only [verticalAxisPoint]
  rw [dist_planeEmbedding_eq_euclideanDistance]
  simp [euclideanDistance, squaredDistance, Real.sqrt_sq_eq_abs]

lemma intrinsicShearMap_verticalAxis_neg_one (amplitude : ℝ) :
    intrinsicShearMap amplitude (verticalAxisPoint (-1)) = verticalAxisPoint (-1) := by
  ext i
  fin_cases i <;>
    simp [intrinsicShearMap, shearKernel, verticalAxisPoint, planeEmbedding, tentBump]

lemma intrinsicShearMap_verticalAxis_zero (amplitude : ℝ) :
    intrinsicShearMap amplitude (verticalAxisPoint 0) = verticalAxisPoint amplitude := by
  ext i
  fin_cases i <;>
    simp [intrinsicShearMap, shearKernel, verticalAxisPoint, planeEmbedding, tentBump]

lemma intrinsicShearMap_verticalAxis_one (amplitude : ℝ) :
    intrinsicShearMap amplitude (verticalAxisPoint 1) = verticalAxisPoint 1 := by
  ext i
  fin_cases i <;>
    simp [intrinsicShearMap, shearKernel, verticalAxisPoint, planeEmbedding, tentBump]

/-- No global direct coefficient can beat the exact expanding fiber slope `1+a`. -/
theorem forward_constant_ge_one_add_amplitude
    (amplitude constant : ℝ) (hAmplitude : 0 ≤ amplitude)
    (hBound : ∀ first second,
      dist (intrinsicShearMap amplitude first) (intrinsicShearMap amplitude second) ≤
        constant * dist first second) :
    1 + amplitude ≤ constant := by
  have h := hBound (verticalAxisPoint (-1)) (verticalAxisPoint 0)
  rw [intrinsicShearMap_verticalAxis_neg_one,
    intrinsicShearMap_verticalAxis_zero,
    verticalAxisPoint_dist, verticalAxisPoint_dist] at h
  have hNeg : -1 - amplitude ≤ 0 := by linarith
  norm_num [abs_of_nonpos hNeg] at h
  nlinarith

/-- No inverse coefficient can beat the exact contracting fiber slope `1-a`. -/
theorem inverse_constant_ge_inv_one_sub_amplitude
    (amplitude constant : ℝ)
    (hBelowOne : amplitude < 1)
    (hBound : ∀ first second,
      dist first second ≤ constant *
        dist (intrinsicShearMap amplitude first) (intrinsicShearMap amplitude second)) :
    1 / (1 - amplitude) ≤ constant := by
  have h := hBound (verticalAxisPoint 0) (verticalAxisPoint 1)
  rw [intrinsicShearMap_verticalAxis_zero,
    intrinsicShearMap_verticalAxis_one,
    verticalAxisPoint_dist, verticalAxisPoint_dist] at h
  have hSub : 0 < 1 - amplitude := sub_pos.mpr hBelowOne
  have hNeg : amplitude - 1 ≤ 0 := by linarith
  norm_num [abs_of_nonpos hNeg] at h
  rw [div_le_iff₀ hSub]
  nlinarith

/-- The exact support result and the sharper metric chamber do not claim a physical scale. -/
theorem exact_support_and_metric_chamber
    (amplitude : ℝ) (hAmplitude : 0 < amplitude) :
    closure (intrinsicShearMovingSet amplitude) = intrinsicShearExactCarrier ∧
      frontier intrinsicShearExactCarrier = intrinsicShearSquarePerimeter ∧
      (∀ first second,
        dist (intrinsicShearMap amplitude first) (intrinsicShearMap amplitude second) ≤
          (1 + Real.sqrt 2 * amplitude) * dist first second) ∧
      (∀ first second,
        (1 - Real.sqrt 2 * amplitude) * dist first second ≤
          dist (intrinsicShearMap amplitude first) (intrinsicShearMap amplitude second)) := by
  exact ⟨closure_intrinsicShearMovingSet amplitude hAmplitude,
    frontier_intrinsicShearExactCarrier,
    intrinsicShearMap_dist_le_sqrt_two amplitude hAmplitude.le,
    intrinsicShearMap_colipschitz_sqrt_two amplitude hAmplitude.le⟩

end BoundaryOfSelf.IntrinsicNonradialShearExactSupport
