import IntrinsicNonradialShearRealizableBlowUp

open scoped Topology RealInnerProductSpace
open Set Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearRealizableClosure

noncomputable section

open StandardHausdorffMetricBridge
open CompactTentHomeomorphism
open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearKernelSharp
open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearDiagonalBlowUpInverse
open IntrinsicNonradialShearRealizableBlowUp

/-! ## IF-BS-22F-F8C15: exact realizable closure -/

def directionWidth (direction : AmbientPlane) : ℝ :=
  |direction.ofLp 0| + |direction.ofLp 1|

def directionProduct (direction : AmbientPlane) : ℝ :=
  |direction.ofLp 0| * |direction.ofLp 1|

def chordSlopeAlong
    (direction : AmbientPlane)
    (scale : ℝ)
    (base : AmbientPlane) : ℝ :=
  (shearKernel base - shearKernel (base - scale • direction)) / scale

lemma unit_coordinate_abs_le_one
    {direction : AmbientPlane}
    (hunit : direction.ofLp 0 ^ 2 + direction.ofLp 1 ^ 2 = 1) :
    |direction.ofLp 0| ≤ 1 ∧ |direction.ofLp 1| ≤ 1 := by
  have hx_sq : direction.ofLp 0 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (direction.ofLp 1)]
  have hy_sq : direction.ofLp 1 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (direction.ofLp 0)]
  constructor
  · exact (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
      (by simpa [sq_abs] using hx_sq)
  · exact (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
      (by simpa [sq_abs] using hy_sq)

lemma directionWidth_pos
    {direction : AmbientPlane}
    (hunit : direction.ofLp 0 ^ 2 + direction.ofLp 1 ^ 2 = 1) :
    0 < directionWidth direction := by
  have hsum : |direction.ofLp 0| + |direction.ofLp 1| ≠ 0 := by
    intro hzero
    have hx0 : |direction.ofLp 0| = 0 := by
      nlinarith [abs_nonneg (direction.ofLp 0), abs_nonneg (direction.ofLp 1)]
    have hy0 : |direction.ofLp 1| = 0 := by
      nlinarith [abs_nonneg (direction.ofLp 0), abs_nonneg (direction.ofLp 1)]
    rw [abs_eq_zero.mp hx0, abs_eq_zero.mp hy0] at hunit
    norm_num at hunit
  simpa [directionWidth] using
    (lt_of_le_of_ne
      (add_nonneg (abs_nonneg (direction.ofLp 0)) (abs_nonneg (direction.ofLp 1)))
      (Ne.symm hsum))

lemma directionWidth_le_two
    {direction : AmbientPlane}
    (hunit : direction.ofLp 0 ^ 2 + direction.ofLp 1 ^ 2 = 1) :
    directionWidth direction ≤ 2 := by
  rcases unit_coordinate_abs_le_one hunit with ⟨hx, hy⟩
  simp only [directionWidth]
  linarith

lemma directionProduct_nonneg (direction : AmbientPlane) :
    0 ≤ directionProduct direction := by
  exact mul_nonneg (abs_nonneg _) (abs_nonneg _)

lemma norm_eq_one_of_coordinate_unit
    {direction : AmbientPlane}
    (hunit : direction.ofLp 0 ^ 2 + direction.ofLp 1 ^ 2 = 1) :
    ‖direction‖ = 1 := by
  have hnorm_sq : ‖direction‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] using hunit
  nlinarith [norm_nonneg direction]

lemma dist_base_sub_scaledDirection
    (base direction : AmbientPlane)
    {scale : ℝ}
    (hscale : 0 ≤ scale)
    (hunit : direction.ofLp 0 ^ 2 + direction.ofLp 1 ^ 2 = 1) :
    dist base (base - scale • direction) = scale := by
  rw [dist_eq_norm]
  have hnorm := norm_eq_one_of_coordinate_unit hunit
  calc
    ‖base - (base - scale • direction)‖ = ‖scale • direction‖ := by congr 1 <;> abel
    _ = |scale| * ‖direction‖ := norm_smul scale direction
    _ = scale := by rw [abs_of_nonneg hscale, hnorm]; ring

lemma shearKernel_scaled_unit
    {direction : AmbientPlane}
    {scale : ℝ}
    (hscale0 : 0 ≤ scale)
    (hscale1 : scale ≤ 1)
    (hunit : direction.ofLp 0 ^ 2 + direction.ofLp 1 ^ 2 = 1) :
    shearKernel (scale • direction) =
      (1 - scale * |direction.ofLp 0|) *
        (1 - scale * |direction.ofLp 1|) := by
  rcases unit_coordinate_abs_le_one hunit with ⟨hx, hy⟩
  have htx : scale * |direction.ofLp 0| ≤ 1 := by
    nlinarith [mul_nonneg hscale0 (abs_nonneg (direction.ofLp 0)),
      mul_nonneg (sub_nonneg.mpr hscale1) (sub_nonneg.mpr hx)]
  have hty : scale * |direction.ofLp 1| ≤ 1 := by
    nlinarith [mul_nonneg hscale0 (abs_nonneg (direction.ofLp 1)),
      mul_nonneg (sub_nonneg.mpr hscale1) (sub_nonneg.mpr hy)]
  simp [shearKernel, tentBump, abs_mul, abs_of_nonneg hscale0,
    max_eq_right (sub_nonneg.mpr htx), max_eq_right (sub_nonneg.mpr hty)]

lemma shearKernel_neg_scaled_unit
    {direction : AmbientPlane}
    {scale : ℝ}
    (hscale0 : 0 ≤ scale)
    (hscale1 : scale ≤ 1)
    (hunit : direction.ofLp 0 ^ 2 + direction.ofLp 1 ^ 2 = 1) :
    shearKernel (-(scale • direction)) =
      (1 - scale * |direction.ofLp 0|) *
        (1 - scale * |direction.ofLp 1|) := by
  have hunit_neg :
      (-direction).ofLp 0 ^ 2 + (-direction).ofLp 1 ^ 2 = 1 := by
    simpa using hunit
  rw [show -(scale • direction) = scale • (-direction) by simp]
  rw [shearKernel_scaled_unit hscale0 hscale1 hunit_neg]
  simp

lemma continuous_shearKernel : Continuous shearKernel := by
  apply Continuous.mul
  · exact tentBump_lipschitz.continuous.comp
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)
  · exact tentBump_lipschitz.continuous.comp
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)

lemma continuous_chordSlopeAlong
    (direction : AmbientPlane)
    (scale : ℝ) :
    Continuous (chordSlopeAlong direction scale) := by
  exact (continuous_shearKernel.sub
    (continuous_shearKernel.comp (continuous_id.sub continuous_const))).div_const scale

def finiteDirectionalMargin (direction : AmbientPlane) (scale : ℝ) : ℝ :=
  directionWidth direction - scale * directionProduct direction

lemma chordSlopeAlong_zero
    {direction : AmbientPlane}
    {scale : ℝ}
    (hscale0 : 0 < scale)
    (hscale1 : scale ≤ 1)
    (hunit : direction.ofLp 0 ^ 2 + direction.ofLp 1 ^ 2 = 1) :
    chordSlopeAlong direction scale 0 = finiteDirectionalMargin direction scale := by
  rw [chordSlopeAlong]
  have hk0 : shearKernel (0 : AmbientPlane) = 1 := by
    simpa [kernelOrigin_eq_zero] using shearKernel_kernelOrigin
  rw [hk0]
  have hneg : (0 : AmbientPlane) - scale • direction = -(scale • direction) := by abel
  rw [hneg, shearKernel_neg_scaled_unit (le_of_lt hscale0) hscale1 hunit]
  unfold finiteDirectionalMargin directionWidth directionProduct
  field_simp [hscale0.ne']
  ring

lemma chordSlopeAlong_scaled
    {direction : AmbientPlane}
    {scale : ℝ}
    (hscale0 : 0 < scale)
    (hscale1 : scale ≤ 1)
    (hunit : direction.ofLp 0 ^ 2 + direction.ofLp 1 ^ 2 = 1) :
    chordSlopeAlong direction scale (scale • direction) =
      -finiteDirectionalMargin direction scale := by
  rw [chordSlopeAlong]
  have hk0 : shearKernel (0 : AmbientPlane) = 1 := by
    simpa [kernelOrigin_eq_zero] using shearKernel_kernelOrigin
  have hsub : scale • direction - scale • direction = (0 : AmbientPlane) := sub_self _
  rw [hsub, hk0, shearKernel_scaled_unit (le_of_lt hscale0) hscale1 hunit]
  unfold finiteDirectionalMargin directionWidth directionProduct
  field_simp [hscale0.ne']
  ring

theorem exists_base_with_chordSlope
    {direction : AmbientPlane}
    {scale target : ℝ}
    (hscale0 : 0 < scale)
    (hscale1 : scale ≤ 1)
    (hunit : direction.ofLp 0 ^ 2 + direction.ofLp 1 ^ 2 = 1)
    (htarget : |target| ≤ finiteDirectionalMargin direction scale) :
    ∃ base : AmbientPlane, chordSlopeAlong direction scale base = target := by
  have hlower : -finiteDirectionalMargin direction scale ≤ target :=
    (abs_le.mp htarget).1
  have hupper : target ≤ finiteDirectionalMargin direction scale :=
    (abs_le.mp htarget).2
  have hinterval : target ∈ Set.Icc
      (chordSlopeAlong direction scale (scale • direction))
      (chordSlopeAlong direction scale 0) := by
    rw [chordSlopeAlong_scaled hscale0 hscale1 hunit,
      chordSlopeAlong_zero hscale0 hscale1 hunit]
    exact ⟨hlower, hupper⟩
  rcases intermediate_value_univ (scale • direction) 0
      (continuous_chordSlopeAlong direction scale) hinterval with
    ⟨base, hbase⟩
  exact ⟨base, hbase⟩

lemma chordBlowUp_base_sub_scaledDirection
    {direction base : AmbientPlane}
    {scale target : ℝ}
    (hscale0 : 0 < scale)
    (hunit : direction.ofLp 0 ^ 2 + direction.ofLp 1 ^ 2 = 1)
    (hslope : chordSlopeAlong direction scale base = target) :
    chordBlowUp base (base - scale • direction) = (direction, target) := by
  have hdist := dist_base_sub_scaledDirection base direction (le_of_lt hscale0) hunit
  apply Prod.ext
  · change normalizedChordDirection base (base - scale • direction) = direction
    unfold normalizedChordDirection
    rw [hdist]
    ext index
    fin_cases index <;> simp [planeEmbedding] <;> field_simp [hscale0.ne']
  · change normalizedKernelSlope base (base - scale • direction) = target
    unfold normalizedKernelSlope
    rw [hdist]
    exact hslope

theorem strictDiamondRecord_is_realisable
    {direction : AmbientPlane}
    {target : ℝ}
    (hunit : direction.ofLp 0 ^ 2 + direction.ofLp 1 ^ 2 = 1)
    (hstrict : |target| < directionWidth direction) :
    (direction, target) ∈ RealizableChordRecords := by
  let gap : ℝ := directionWidth direction - |target|
  let product : ℝ := directionProduct direction
  let scale : ℝ := gap / (2 * (product + 1))
  have hgap : 0 < gap := by simpa [gap] using sub_pos.mpr hstrict
  have hproduct : 0 ≤ product := by
    simpa [product] using directionProduct_nonneg direction
  have hden : 0 < 2 * (product + 1) := by positivity
  have hscale0 : 0 < scale := div_pos hgap hden
  have hgap_le_two : gap ≤ 2 := by
    dsimp [gap]
    have := directionWidth_le_two hunit
    nlinarith [abs_nonneg target]
  have hscale1 : scale ≤ 1 := by
    dsimp [scale]
    rw [div_le_iff₀ hden]
    nlinarith
  have hratio : product / (2 * (product + 1)) < 1 := by
    rw [div_lt_one hden]
    nlinarith
  have hscale_product : scale * product < gap := by
    have hmul := mul_lt_mul_of_pos_left hratio hgap
    dsimp [scale]
    calc
      gap / (2 * (product + 1)) * product =
          gap * (product / (2 * (product + 1))) := by ring
      _ < gap * 1 := hmul
      _ = gap := by ring
  have htarget : |target| ≤ finiteDirectionalMargin direction scale := by
    dsimp [finiteDirectionalMargin, gap] at hscale_product ⊢
    linarith
  rcases exists_base_with_chordSlope hscale0 hscale1 hunit htarget with
    ⟨base, hbase⟩
  refine ⟨base, base - scale • direction, ?_, ?_⟩
  · exact dist_ne_zero.mp (by
      rw [dist_base_sub_scaledDirection base direction (le_of_lt hscale0) hunit]
      exact hscale0.ne')
  · exact chordBlowUp_base_sub_scaledDirection hscale0 hunit hbase

def interiorSlopeSequence (target : ℝ) (index : ℕ) : ℝ :=
  (1 - diagonalScale index) * target

lemma interiorSlopeSequence_tendsto (target : ℝ) :
    Tendsto (interiorSlopeSequence target) atTop (𝓝 target) := by
  unfold interiorSlopeSequence
  convert (tendsto_const_nhds.sub diagonalScale_tendsto_zero).mul_const target using 1 <;>
    ring

theorem directionalDiamondBand_subset_realisableClosure :
    directionalDiamondBand ⊆ closure RealizableChordRecords := by
  intro record hrecord
  have hunit := (chamber_unit_and_slope hrecord.1).1
  have hwidth_pos := directionWidth_pos hunit
  have hslope : |record.2| ≤ directionWidth record.1 := hrecord.2
  rcases lt_or_eq_of_le hslope with hstrict | hboundary
  · apply subset_closure
    simpa [Prod.eta] using strictDiamondRecord_is_realisable hunit hstrict
  · rw [mem_closure_iff_seq_limit]
    let sequence : ℕ → BlowUpPoint := fun index =>
      (record.1, interiorSlopeSequence record.2 index)
    refine ⟨sequence, ?_, ?_⟩
    · intro index
      apply strictDiamondRecord_is_realisable hunit
      have hscale_pos := diagonalScale_pos index
      have hscale_le := diagonalScale_le_one index
      have hfactor_nonneg : 0 ≤ 1 - diagonalScale index := sub_nonneg.mpr hscale_le
      have hfactor_lt : 1 - diagonalScale index < 1 := by linarith
      rw [interiorSlopeSequence, abs_mul, abs_of_nonneg hfactor_nonneg, hboundary]
      nlinarith
    · have hslope_tendsto := interiorSlopeSequence_tendsto record.2
      simpa [sequence, Prod.eta] using
        Filter.Tendsto.prodMk_nhds tendsto_const_nhds hslope_tendsto

theorem realizableClosure_eq_directionalDiamondBand :
    closure RealizableChordRecords = directionalDiamondBand := by
  apply Set.Subset.antisymm
  · exact realizableClosure_subset_directionalDiamond
  · exact directionalDiamondBand_subset_realisableClosure

end

end BoundaryOfSelf.IntrinsicNonradialShearRealizableClosure
