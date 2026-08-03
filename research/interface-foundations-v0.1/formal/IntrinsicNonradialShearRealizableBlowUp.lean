import IntrinsicNonradialShearDiagonalBlowUpInverse

open scoped Topology RealInnerProductSpace
open Set Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearRealizableBlowUp

noncomputable section

open StandardHausdorffMetricBridge
open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearExactSupport
open IntrinsicNonradialShearKernelSharp
open IntrinsicNonradialShearSpectralMap
open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearDiagonalBlowUpInverse

/-! ## IF-BS-22F-F8C14: realizable blow-up outer hull and attainable poles -/

/-- Records produced by actual nonzero finite chords. -/
def RealizableChordRecords : Set BlowUpPoint :=
  {record | ∃ first second : AmbientPlane,
    first ≠ second ∧ chordBlowUp first second = record}

/-- The directional diamond refines the uniform relaxed slope strip. -/
def directionalDiamondBand : Set BlowUpPoint :=
  directionalBlowUpChamber ∩
    {record | |record.2| ≤ |record.1.ofLp 0| + |record.1.ofLp 1|}

theorem chord_normalizedSlope_le_directionalDiamond
    {first second : AmbientPlane}
    (hne : first ≠ second) :
    |normalizedKernelSlope first second| ≤
      |(normalizedChordDirection first second).ofLp 0| +
        |(normalizedChordDirection first second).ofLp 1| := by
  have hdist_pos : 0 < dist first second := dist_pos.mpr hne
  have hkernel := shearKernel_abs_sub_le_coordinate_sum first second
  have hdiv := div_le_div_of_nonneg_right hkernel (le_of_lt hdist_pos)
  simpa [normalizedKernelSlope, normalizedChordDirection, planeEmbedding,
    abs_div, abs_of_nonneg (dist_nonneg : 0 ≤ dist first second),
    add_div] using hdiv

theorem chordBlowUp_mem_directionalDiamond
    {first second : AmbientPlane}
    (hne : first ≠ second) :
    chordBlowUp first second ∈ directionalDiamondBand := by
  exact ⟨chordBlowUp_mem_chamber hne,
    chord_normalizedSlope_le_directionalDiamond hne⟩

theorem realizableChordRecords_subset_directionalDiamond :
    RealizableChordRecords ⊆ directionalDiamondBand := by
  intro record hrecord
  rcases hrecord with ⟨first, second, hne, rfl⟩
  exact chordBlowUp_mem_directionalDiamond hne

lemma continuous_direction_zero :
    Continuous (fun record : BlowUpPoint => record.1.ofLp 0) := by
  exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp
    (continuous_fst : Continuous (fun record : BlowUpPoint => record.1))

lemma continuous_direction_one :
    Continuous (fun record : BlowUpPoint => record.1.ofLp 1) := by
  exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
    (continuous_fst : Continuous (fun record : BlowUpPoint => record.1))

theorem directionalDiamondBand_isClosed : _root_.IsClosed directionalDiamondBand := by
  apply directionalBlowUpChamber_compact.isClosed.inter
  exact isClosed_le continuous_snd.abs
    (continuous_direction_zero.abs.add continuous_direction_one.abs)

theorem directionalDiamondBand_compact : IsCompact directionalDiamondBand :=
  directionalBlowUpChamber_compact.of_isClosed_subset
    directionalDiamondBand_isClosed (fun _ hrecord => hrecord.1)

theorem realizableClosure_subset_directionalDiamond :
    closure RealizableChordRecords ⊆ directionalDiamondBand :=
  closure_minimal realizableChordRecords_subset_directionalDiamond
    directionalDiamondBand_isClosed

lemma one_lt_sqrt_two : 1 < Real.sqrt 2 := by
  nlinarith [IntrinsicNonradialShearDiagonalBlowUpInverse.sqrt_two_sq,
    IntrinsicNonradialShearDiagonalBlowUpInverse.sqrt_two_nonneg]

theorem relaxedLowerWitness_not_directionalDiamond :
    relaxedLowerWitness ∉ directionalDiamondBand := by
  intro hwitness
  have hslope := hwitness.2
  simp [relaxedLowerWitness, planeEmbedding] at hslope
  rw [abs_of_nonneg
    IntrinsicNonradialShearDiagonalBlowUpInverse.sqrt_two_nonneg] at hslope
  linarith [one_lt_sqrt_two]

theorem relaxedUpperWitness_not_directionalDiamond :
    relaxedUpperWitness ∉ directionalDiamondBand := by
  intro hwitness
  have hslope := hwitness.2
  simp [relaxedUpperWitness, planeEmbedding] at hslope
  rw [abs_of_nonneg
    IntrinsicNonradialShearDiagonalBlowUpInverse.sqrt_two_nonneg] at hslope
  linarith [one_lt_sqrt_two]

theorem relaxed_poles_not_realisable_limits :
    relaxedLowerWitness ∉ closure RealizableChordRecords ∧
      relaxedUpperWitness ∉ closure RealizableChordRecords := by
  constructor
  · intro hwitness
    exact relaxedLowerWitness_not_directionalDiamond
      (realizableClosure_subset_directionalDiamond hwitness)
  · intro hwitness
    exact relaxedUpperWitness_not_directionalDiamond
      (realizableClosure_subset_directionalDiamond hwitness)

/-- Positive diagonal direction reached from the negative quadrant. -/
def diagonalPositiveDirection : AmbientPlane :=
  planeEmbedding ⟨(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹⟩

/-- Negative diagonal direction reached from the positive quadrant. -/
def diagonalNegativeDirection : AmbientPlane :=
  planeEmbedding ⟨-(Real.sqrt 2)⁻¹, -(Real.sqrt 2)⁻¹⟩

def attainableUpperPole : BlowUpPoint :=
  (diagonalPositiveDirection, Real.sqrt 2)

def attainableLowerPole : BlowUpPoint :=
  (diagonalNegativeDirection, Real.sqrt 2)

lemma sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := by
  positivity

lemma chordBlowUp_kernelDiagonalPoint_formula
    {t : ℝ}
    (ht0 : 0 < t)
    (ht1 : t ≤ 1) :
    chordBlowUp kernelOrigin (kernelDiagonalPoint t) =
      (diagonalPositiveDirection, (2 - t) / Real.sqrt 2) := by
  apply Prod.ext
  · change normalizedChordDirection kernelOrigin (kernelDiagonalPoint t) =
      diagonalPositiveDirection
    unfold normalizedChordDirection
    rw [dist_kernelOrigin_kernelDiagonalPoint (le_of_lt ht0)]
    ext index
    fin_cases index <;>
      simp [diagonalPositiveDirection, kernelOrigin, kernelDiagonalPoint,
        planeEmbedding] <;>
      field_simp [sqrt_two_ne_zero, ht0.ne']
  · change normalizedKernelSlope kernelOrigin (kernelDiagonalPoint t) =
      (2 - t) / Real.sqrt 2
    unfold normalizedKernelSlope
    rw [shearKernel_kernelOrigin,
      shearKernel_kernelDiagonalPoint (le_of_lt ht0) ht1,
      dist_kernelOrigin_kernelDiagonalPoint (le_of_lt ht0)]
    field_simp [sqrt_two_ne_zero, ht0.ne']
    ring

lemma dist_kernelOrigin_positiveDiagonal
    {t : ℝ}
    (ht0 : 0 ≤ t) :
    dist kernelOrigin (kernelPositiveDirectionalPoint t 1 1) =
      Real.sqrt 2 * t := by
  have hsq := dist_kernelOrigin_kernelPositiveDirectionalPoint_sq t 1 1
  have hleft := dist_nonneg (x := kernelOrigin)
    (y := kernelPositiveDirectionalPoint t 1 1)
  have hright : 0 ≤ Real.sqrt 2 * t :=
    mul_nonneg IntrinsicNonradialShearDiagonalBlowUpInverse.sqrt_two_nonneg ht0
  nlinarith [IntrinsicNonradialShearDiagonalBlowUpInverse.sqrt_two_sq]

lemma chordBlowUp_positiveDiagonalPoint_formula
    {t : ℝ}
    (ht0 : 0 < t)
    (ht1 : t ≤ 1) :
    chordBlowUp kernelOrigin (kernelPositiveDirectionalPoint t 1 1) =
      (diagonalNegativeDirection, (2 - t) / Real.sqrt 2) := by
  apply Prod.ext
  · change normalizedChordDirection kernelOrigin
      (kernelPositiveDirectionalPoint t 1 1) = diagonalNegativeDirection
    unfold normalizedChordDirection
    rw [dist_kernelOrigin_positiveDiagonal (le_of_lt ht0)]
    ext index
    fin_cases index <;>
      simp [diagonalNegativeDirection, kernelOrigin,
        kernelPositiveDirectionalPoint, planeEmbedding] <;>
      field_simp [sqrt_two_ne_zero, ht0.ne']
  · change normalizedKernelSlope kernelOrigin
      (kernelPositiveDirectionalPoint t 1 1) = (2 - t) / Real.sqrt 2
    unfold normalizedKernelSlope
    rw [shearKernel_kernelOrigin,
      shearKernel_kernelPositiveDirectionalPoint (t := t) (x := 1) (y := 1)
        (by simpa using le_of_lt ht0) (by simpa using ht1)
        (by simpa using le_of_lt ht0) (by simpa using ht1),
      dist_kernelOrigin_positiveDiagonal (le_of_lt ht0)]
    field_simp [sqrt_two_ne_zero, ht0.ne']
    ring

def diagonalScale (index : ℕ) : ℝ :=
  ((index : ℝ) + 1)⁻¹

lemma diagonalScale_pos (index : ℕ) : 0 < diagonalScale index := by
  unfold diagonalScale
  positivity

lemma diagonalScale_le_one (index : ℕ) : diagonalScale index ≤ 1 := by
  unfold diagonalScale
  rw [inv_le_one₀ (by positivity : (0 : ℝ) < (index : ℝ) + 1)]
  norm_num

lemma diagonalScale_tendsto_zero :
    Tendsto diagonalScale atTop (𝓝 0) := by
  unfold diagonalScale
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma two_div_sqrt_two : 2 / Real.sqrt 2 = Real.sqrt 2 := by
  field_simp [sqrt_two_ne_zero]
  nlinarith [IntrinsicNonradialShearDiagonalBlowUpInverse.sqrt_two_sq]

theorem attainableUpperPole_mem_closure :
    attainableUpperPole ∈ closure RealizableChordRecords := by
  rw [mem_closure_iff_seq_limit]
  let sequence : ℕ → BlowUpPoint := fun index =>
    chordBlowUp kernelOrigin (kernelDiagonalPoint (diagonalScale index))
  refine ⟨sequence, ?_, ?_⟩
  · intro index
    refine ⟨kernelOrigin, kernelDiagonalPoint (diagonalScale index), ?_, rfl⟩
    exact dist_pos.mp (by
      rw [dist_kernelOrigin_kernelDiagonalPoint (le_of_lt (diagonalScale_pos index))]
      exact mul_pos (by positivity) (diagonalScale_pos index))
  · have hslope : Tendsto (fun index =>
        (2 - diagonalScale index) / Real.sqrt 2) atTop (𝓝 (Real.sqrt 2)) := by
      convert (tendsto_const_nhds.sub diagonalScale_tendsto_zero).div_const
        (Real.sqrt 2) using 1
      simpa [two_div_sqrt_two]
    have hpair : Tendsto (fun index =>
        (diagonalPositiveDirection,
          (2 - diagonalScale index) / Real.sqrt 2)) atTop
        (𝓝 attainableUpperPole) := by
      simpa [attainableUpperPole] using
        Filter.Tendsto.prodMk_nhds tendsto_const_nhds hslope
    apply hpair.congr'
    filter_upwards [] with index
    exact (chordBlowUp_kernelDiagonalPoint_formula
      (diagonalScale_pos index) (diagonalScale_le_one index)).symm

theorem attainableLowerPole_mem_closure :
    attainableLowerPole ∈ closure RealizableChordRecords := by
  rw [mem_closure_iff_seq_limit]
  let sequence : ℕ → BlowUpPoint := fun index =>
    chordBlowUp kernelOrigin
      (kernelPositiveDirectionalPoint (diagonalScale index) 1 1)
  refine ⟨sequence, ?_, ?_⟩
  · intro index
    refine ⟨kernelOrigin,
      kernelPositiveDirectionalPoint (diagonalScale index) 1 1, ?_, rfl⟩
    exact dist_pos.mp (by
      rw [dist_kernelOrigin_positiveDiagonal
        (le_of_lt (diagonalScale_pos index))]
      exact mul_pos (by positivity) (diagonalScale_pos index))
  · have hslope : Tendsto (fun index =>
        (2 - diagonalScale index) / Real.sqrt 2) atTop (𝓝 (Real.sqrt 2)) := by
      convert (tendsto_const_nhds.sub diagonalScale_tendsto_zero).div_const
        (Real.sqrt 2) using 1
      simpa [two_div_sqrt_two]
    have hpair : Tendsto (fun index =>
        (diagonalNegativeDirection,
          (2 - diagonalScale index) / Real.sqrt 2)) atTop
        (𝓝 attainableLowerPole) := by
      simpa [attainableLowerPole] using
        Filter.Tendsto.prodMk_nhds tendsto_const_nhds hslope
    apply hpair.congr'
    filter_upwards [] with index
    exact (chordBlowUp_positiveDiagonalPoint_formula
      (diagonalScale_pos index) (diagonalScale_le_one index)).symm

/-- Boundary record associated with a nonnegative unit direction. -/
def directionalBoundaryTarget (x y : ℝ) : BlowUpPoint :=
  (planeEmbedding ⟨x, y⟩, x + y)

lemma dist_kernelOrigin_directionalPoint
    {t x y : ℝ}
    (ht0 : 0 ≤ t)
    (hunit : x ^ 2 + y ^ 2 = 1) :
    dist kernelOrigin (kernelDirectionalPoint t x y) = t := by
  have hsq := dist_kernelOrigin_kernelDirectionalPoint_sq t x y
  have hdist0 : 0 ≤ dist kernelOrigin (kernelDirectionalPoint t x y) := dist_nonneg
  have hsq' : dist kernelOrigin (kernelDirectionalPoint t x y) ^ 2 = t ^ 2 := by
    calc
      dist kernelOrigin (kernelDirectionalPoint t x y) ^ 2 =
          (t * x) ^ 2 + (t * y) ^ 2 := hsq
      _ = t ^ 2 := by nlinarith
  nlinarith

lemma chordBlowUp_directionalPoint_formula
    {t x y : ℝ}
    (ht0 : 0 < t)
    (hx0 : 0 ≤ x)
    (hy0 : 0 ≤ y)
    (htx1 : t * x ≤ 1)
    (hty1 : t * y ≤ 1)
    (hunit : x ^ 2 + y ^ 2 = 1) :
    chordBlowUp kernelOrigin (kernelDirectionalPoint t x y) =
      (planeEmbedding ⟨x, y⟩, x + y - t * x * y) := by
  apply Prod.ext
  · change normalizedChordDirection kernelOrigin (kernelDirectionalPoint t x y) =
      planeEmbedding ⟨x, y⟩
    unfold normalizedChordDirection
    rw [dist_kernelOrigin_directionalPoint (le_of_lt ht0) hunit]
    ext index
    fin_cases index <;>
      simp [kernelOrigin, kernelDirectionalPoint, planeEmbedding] <;>
      field_simp [ht0.ne']
  · change normalizedKernelSlope kernelOrigin (kernelDirectionalPoint t x y) =
      x + y - t * x * y
    unfold normalizedKernelSlope
    rw [shearKernel_kernelOrigin,
      shearKernel_kernelDirectionalPoint (mul_nonneg (le_of_lt ht0) hx0) htx1
        (mul_nonneg (le_of_lt ht0) hy0) hty1,
      dist_kernelOrigin_directionalPoint (le_of_lt ht0) hunit]
    field_simp [ht0.ne']
    ring

theorem directionalBoundaryTarget_mem_closure
    {x y : ℝ}
    (hx0 : 0 ≤ x)
    (hy0 : 0 ≤ y)
    (hunit : x ^ 2 + y ^ 2 = 1) :
    directionalBoundaryTarget x y ∈ closure RealizableChordRecords := by
  have hx_sq : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg y]
  have hy_sq : y ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hx1 : x ≤ 1 := by nlinarith [sq_nonneg (x - 1)]
  have hy1 : y ≤ 1 := by nlinarith [sq_nonneg (y - 1)]
  rw [mem_closure_iff_seq_limit]
  let sequence : ℕ → BlowUpPoint := fun index =>
    chordBlowUp kernelOrigin
      (kernelDirectionalPoint (diagonalScale index) x y)
  refine ⟨sequence, ?_, ?_⟩
  · intro index
    refine ⟨kernelOrigin,
      kernelDirectionalPoint (diagonalScale index) x y, ?_, rfl⟩
    exact dist_pos.mp (by
      rw [dist_kernelOrigin_directionalPoint
        (le_of_lt (diagonalScale_pos index)) hunit]
      exact diagonalScale_pos index)
  · have hscaled_x : ∀ index, diagonalScale index * x ≤ 1 := by
      intro index
      have hscale0 := le_of_lt (diagonalScale_pos index)
      have hscale1 := diagonalScale_le_one index
      nlinarith [mul_nonneg hscale0 hx0,
        mul_nonneg (sub_nonneg.mpr hscale1) (sub_nonneg.mpr hx1)]
    have hscaled_y : ∀ index, diagonalScale index * y ≤ 1 := by
      intro index
      have hscale0 := le_of_lt (diagonalScale_pos index)
      have hscale1 := diagonalScale_le_one index
      nlinarith [mul_nonneg hscale0 hy0,
        mul_nonneg (sub_nonneg.mpr hscale1) (sub_nonneg.mpr hy1)]
    have hslope : Tendsto (fun index =>
        x + y - diagonalScale index * x * y) atTop (𝓝 (x + y)) := by
      convert tendsto_const_nhds.sub
        ((diagonalScale_tendsto_zero.mul_const x).mul_const y) using 1 <;>
        ring
    have hpair : Tendsto (fun index =>
        (planeEmbedding ⟨x, y⟩,
          x + y - diagonalScale index * x * y)) atTop
        (𝓝 (directionalBoundaryTarget x y)) := by
      simpa [directionalBoundaryTarget] using
        Filter.Tendsto.prodMk_nhds tendsto_const_nhds hslope
    apply hpair.congr'
    filter_upwards [] with index
    exact (chordBlowUp_directionalPoint_formula
      (diagonalScale_pos index) hx0 hy0 (hscaled_x index) (hscaled_y index)
      hunit).symm

theorem nonnegative_unit_boundary_arc_is_realisable :
    {record | ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ x ^ 2 + y ^ 2 = 1 ∧
      record = directionalBoundaryTarget x y} ⊆
      closure RealizableChordRecords := by
  intro record hrecord
  rcases hrecord with ⟨x, y, hx0, hy0, hunit, rfl⟩
  exact directionalBoundaryTarget_mem_closure hx0 hy0 hunit

end

end BoundaryOfSelf.IntrinsicNonradialShearRealizableBlowUp
