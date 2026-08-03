import IntrinsicNonradialShearClosedCore

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearDiagonalBlowUp

open LocalSegmentRealCompletion
open StandardHausdorffMetricBridge
open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearExactSupport
open IntrinsicNonradialShearKernelSharp
open IntrinsicNonradialShearSpectralMap
open IntrinsicNonradialShearDeltaNet
open IntrinsicNonradialShearClosedCore

abbrev BlowUpPoint := AmbientPlane × ℝ

def directionalBlowUpChamber : Set BlowUpPoint :=
  Metric.sphere kernelOrigin 1 ×ˢ
    Set.Icc (-Real.sqrt 2) (Real.sqrt 2)

theorem directionalBlowUpChamber_compact :
    IsCompact directionalBlowUpChamber := by
  exact (isCompact_sphere kernelOrigin 1).prod isCompact_Icc

noncomputable def normalizedChordDirection
    (first second : AmbientPlane) : AmbientPlane :=
  planeEmbedding
    ({
      x := (first.ofLp 0 - second.ofLp 0) / dist first second
      y := (first.ofLp 1 - second.ofLp 1) / dist first second
    } : RealPlanePoint)

noncomputable def normalizedKernelSlope
    (first second : AmbientPlane) : ℝ :=
  (shearKernel first - shearKernel second) / dist first second

noncomputable def chordBlowUp
    (first second : AmbientPlane) : BlowUpPoint :=
  (normalizedChordDirection first second,
    normalizedKernelSlope first second)

theorem normalizedChordDirection_mem_sphere
    {first second : AmbientPlane} (hne : first ≠ second) :
    normalizedChordDirection first second ∈
      Metric.sphere kernelOrigin 1 := by
  have hdistPos : 0 < dist first second := dist_pos.mpr hne
  have hdistNe : dist first second ≠ 0 := ne_of_gt hdistPos
  have hsource := dist_sq_eq_coordinate_sq_sum first second
  have hsquare :
      dist kernelOrigin (normalizedChordDirection first second) ^ 2 = 1 := by
    rw [dist_sq_eq_coordinate_sq_sum]
    simp [kernelOrigin, normalizedChordDirection, planeEmbedding]
    field_simp [hdistNe]
    nlinarith
  rw [Metric.mem_sphere]
  rw [dist_comm]
  have hnonnegative :
      0 ≤ dist kernelOrigin (normalizedChordDirection first second) :=
    dist_nonneg
  nlinarith

theorem normalizedKernelSlope_mem_Icc
    {first second : AmbientPlane} (hne : first ≠ second) :
    normalizedKernelSlope first second ∈
      Set.Icc (-Real.sqrt 2) (Real.sqrt 2) := by
  have hdistPos : 0 < dist first second := dist_pos.mpr hne
  have hkernel := shearKernel_abs_sub_le_sqrt_two first second
  have habs :
      |normalizedKernelSlope first second| ≤ Real.sqrt 2 := by
    rw [normalizedKernelSlope, abs_div, abs_of_pos hdistPos]
    exact (div_le_iff₀ hdistPos).2 hkernel
  exact abs_le.mp habs

theorem chordBlowUp_mem_chamber
    {first second : AmbientPlane} (hne : first ≠ second) :
    chordBlowUp first second ∈ directionalBlowUpChamber :=
  ⟨normalizedChordDirection_mem_sphere hne,
    normalizedKernelSlope_mem_Icc hne⟩

def forwardBlowUpSq (amplitude : ℝ) (point : BlowUpPoint) : ℝ :=
  point.1.ofLp 0 ^ 2 +
    (point.1.ofLp 1 + amplitude * point.2) ^ 2

theorem chordBlowUp_forward_sq_identity
    (amplitude : ℝ) {first second : AmbientPlane}
    (hne : first ≠ second) :
    dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second) ^ 2 =
      forwardBlowUpSq amplitude (chordBlowUp first second) *
        dist first second ^ 2 := by
  have hdistNe : dist first second ≠ 0 := dist_ne_zero.mpr hne
  rw [intrinsicShearMap_dist_sq_eq]
  simp [forwardBlowUpSq, chordBlowUp, normalizedChordDirection,
    normalizedKernelSlope, planeEmbedding]
  field_simp [hdistNe]

lemma direction_x_abs_le_one
    {direction : AmbientPlane}
    (hdirection : direction ∈ Metric.sphere kernelOrigin 1) :
    |direction.ofLp 0| ≤ 1 := by
  rw [Metric.mem_sphere] at hdirection
  rw [dist_comm] at hdirection
  have hsquare := dist_sq_eq_coordinate_sq_sum kernelOrigin direction
  rw [hdirection] at hsquare
  simp [kernelOrigin, planeEmbedding] at hsquare
  nlinarith [sq_abs (direction.ofLp 0), sq_nonneg (direction.ofLp 1)]

lemma direction_y_abs_le_one
    {direction : AmbientPlane}
    (hdirection : direction ∈ Metric.sphere kernelOrigin 1) :
    |direction.ofLp 1| ≤ 1 := by
  rw [Metric.mem_sphere] at hdirection
  rw [dist_comm] at hdirection
  have hsquare := dist_sq_eq_coordinate_sq_sum kernelOrigin direction
  rw [hdirection] at hsquare
  simp [kernelOrigin, planeEmbedding] at hsquare
  nlinarith [sq_abs (direction.ofLp 1), sq_nonneg (direction.ofLp 0)]

lemma direction_x_sub_abs_le_dist
    (first second : AmbientPlane) :
    |first.ofLp 0 - second.ofLp 0| ≤ dist first second := by
  have hsquare := dist_sq_eq_coordinate_sq_sum first second
  nlinarith [sq_abs (first.ofLp 0 - second.ofLp 0),
    sq_nonneg (first.ofLp 1 - second.ofLp 1),
    (dist_nonneg : 0 ≤ dist first second)]

lemma direction_y_sub_abs_le_dist
    (first second : AmbientPlane) :
    |first.ofLp 1 - second.ofLp 1| ≤ dist first second := by
  have hsquare := dist_sq_eq_coordinate_sq_sum first second
  nlinarith [sq_abs (first.ofLp 1 - second.ofLp 1),
    sq_nonneg (first.ofLp 0 - second.ofLp 0),
    (dist_nonneg : 0 ≤ dist first second)]

lemma blowUp_direction_dist_le
    (first second : BlowUpPoint) :
    dist first.1 second.1 ≤ dist first second := by
  rw [Prod.dist_eq]
  exact le_max_left _ _

lemma blowUp_x_sub_abs_le_dist
    (first second : BlowUpPoint) :
    |first.1.ofLp 0 - second.1.ofLp 0| ≤ dist first second :=
  (direction_x_sub_abs_le_dist first.1 second.1).trans
    (blowUp_direction_dist_le first second)

lemma blowUp_y_sub_abs_le_dist
    (first second : BlowUpPoint) :
    |first.1.ofLp 1 - second.1.ofLp 1| ≤ dist first second :=
  (direction_y_sub_abs_le_dist first.1 second.1).trans
    (blowUp_direction_dist_le first second)

lemma blowUp_slope_sub_abs_le_dist
    (first second : BlowUpPoint) :
    |first.2 - second.2| ≤ dist first second := by
  rw [← Real.dist_eq]
  rw [Prod.dist_eq]
  exact le_max_right _ _

def forwardBlowUpSqRegularity (amplitude : ℝ) : ℝ :=
  2 + 4 * (1 + amplitude) ^ 2

theorem forwardBlowUpSq_regularity_bound
    {amplitude : ℝ} (ha : 0 ≤ amplitude) :
    ∀ first ∈ directionalBlowUpChamber,
      ∀ second ∈ directionalBlowUpChamber,
        |forwardBlowUpSq amplitude first -
            forwardBlowUpSq amplitude second| ≤
          forwardBlowUpSqRegularity amplitude * dist first second := by
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
  have hD0 : 0 ≤ D := dist_nonneg
  have hx₁ : |x₁| ≤ 1 := direction_x_abs_le_one hfirst.1
  have hy₁ : |y₁| ≤ 1 := direction_y_abs_le_one hfirst.1
  have hx₂ : |x₂| ≤ 1 := direction_x_abs_le_one hsecond.1
  have hy₂ : |y₂| ≤ 1 := direction_y_abs_le_one hsecond.1
  have hs₁ : |s₁| ≤ Real.sqrt 2 := abs_le.2 hfirst.2
  have hs₂ : |s₂| ≤ Real.sqrt 2 := abs_le.2 hsecond.2
  have hxDifference : |x₁ - x₂| ≤ D :=
    blowUp_x_sub_abs_le_dist first second
  have hyDifference : |y₁ - y₂| ≤ D :=
    blowUp_y_sub_abs_le_dist first second
  have hsDifference : |s₁ - s₂| ≤ D :=
    blowUp_slope_sub_abs_le_dist first second
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtTwo : Real.sqrt 2 ≤ 2 := by nlinarith
  have hv₁ : |v₁| ≤ 2 * (1 + amplitude) := by
    calc
      |v₁| = |y₁ + amplitude * s₁| := rfl
      _ ≤ |y₁| + |amplitude * s₁| := abs_add_le _ _
      _ = |y₁| + amplitude * |s₁| := by
        rw [abs_mul, abs_of_nonneg ha]
      _ ≤ 1 + amplitude * Real.sqrt 2 := by
        exact add_le_add hy₁ (mul_le_mul_of_nonneg_left hs₁ ha)
      _ ≤ 2 * (1 + amplitude) := by nlinarith
  have hv₂ : |v₂| ≤ 2 * (1 + amplitude) := by
    calc
      |v₂| = |y₂ + amplitude * s₂| := rfl
      _ ≤ |y₂| + |amplitude * s₂| := abs_add_le _ _
      _ = |y₂| + amplitude * |s₂| := by
        rw [abs_mul, abs_of_nonneg ha]
      _ ≤ 1 + amplitude * Real.sqrt 2 := by
        exact add_le_add hy₂ (mul_le_mul_of_nonneg_left hs₂ ha)
      _ ≤ 2 * (1 + amplitude) := by nlinarith
  have hvDifference : |v₁ - v₂| ≤ (1 + amplitude) * D := by
    calc
      |v₁ - v₂| = |(y₁ - y₂) + amplitude * (s₁ - s₂)| := by
        congr 1
        dsimp [v₁, v₂]
        ring
      _ ≤ |y₁ - y₂| + |amplitude * (s₁ - s₂)| := abs_add_le _ _
      _ = |y₁ - y₂| + amplitude * |s₁ - s₂| := by
        rw [abs_mul, abs_of_nonneg ha]
      _ ≤ D + amplitude * D := by
        exact add_le_add hyDifference
          (mul_le_mul_of_nonneg_left hsDifference ha)
      _ = (1 + amplitude) * D := by ring
  have hxSum : |x₁ + x₂| ≤ 2 := by
    calc
      |x₁ + x₂| ≤ |x₁| + |x₂| := abs_add_le _ _
      _ ≤ 2 := by linarith
  have hvSum : |v₁ + v₂| ≤ 4 * (1 + amplitude) := by
    calc
      |v₁ + v₂| ≤ |v₁| + |v₂| := abs_add_le _ _
      _ ≤ 4 * (1 + amplitude) := by linarith
  have hxSquareDifference :
      |x₁ ^ 2 - x₂ ^ 2| ≤ 2 * D := by
    rw [show x₁ ^ 2 - x₂ ^ 2 = (x₁ - x₂) * (x₁ + x₂) by ring]
    rw [abs_mul]
    have hmul := mul_le_mul hxDifference hxSum (abs_nonneg _) hD0
    nlinarith
  have hvRight0 : 0 ≤ (1 + amplitude) * D :=
    mul_nonneg (by linarith) hD0
  have hvSquareDifference :
      |v₁ ^ 2 - v₂ ^ 2| ≤ 4 * (1 + amplitude) ^ 2 * D := by
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
    _ ≤ 2 * D + 4 * (1 + amplitude) ^ 2 * D :=
      add_le_add hxSquareDifference hvSquareDifference
    _ = forwardBlowUpSqRegularity amplitude * dist first second := by
      dsimp [forwardBlowUpSqRegularity, D]
      ring

theorem forwardBlowUpSq_regularityCertificate
    {amplitude : ℝ} (ha : 0 ≤ amplitude)
    (sample : List (NoisyUpperReading BlowUpPoint))
    (hinside : SampleInside directionalBlowUpChamber sample) :
    RegularityCertificate directionalBlowUpChamber sample
      (forwardBlowUpSqRegularity amplitude)
      (forwardBlowUpSq amplitude) := by
  intro point hpoint reading hreading
  exact forwardBlowUpSq_regularity_bound ha point hpoint
    reading.point (hinside reading hreading)

lemma forwardBlowUpSqRegularity_nonneg
    {amplitude : ℝ} (ha : 0 ≤ amplitude) :
    0 ≤ forwardBlowUpSqRegularity amplitude := by
  dsimp [forwardBlowUpSqRegularity]
  positivity

theorem exists_forwardBlowUpSq_finiteCertificate
    {amplitude delta : ℝ}
    (ha : 0 ≤ amplitude) (hdelta : 0 < delta) :
    ∃ sample : List (NoisyUpperReading BlowUpPoint),
      NoisyUpperSampleValid (forwardBlowUpSq amplitude) sample ∧
        DeltaCoverage directionalBlowUpChamber sample delta ∧
          SampleInside directionalBlowUpChamber sample ∧
            RegularityCertificate directionalBlowUpChamber sample
              (forwardBlowUpSqRegularity amplitude)
              (forwardBlowUpSq amplitude) ∧
              ∀ point, point ∈ directionalBlowUpChamber →
                forwardBlowUpSq amplitude point ≤
                  noisySampleUpper sample +
                    forwardBlowUpSqRegularity amplitude * delta := by
  rcases compact_exists_finite_exactSample
      directionalBlowUpChamber_compact hdelta
      (forwardBlowUpSq amplitude) with
    ⟨sample, hvalid, hcoverage, hinside⟩
  have hregular :=
    forwardBlowUpSq_regularityCertificate ha sample hinside
  refine ⟨sample, hvalid, hcoverage, hinside, hregular, ?_⟩
  intro point hpoint
  exact global_le_noisySampleUpper_add_regularity
    (forwardBlowUpSqRegularity_nonneg ha)
    hvalid hcoverage hregular point hpoint

theorem chord_sq_bound_of_blowUp_upper
    {amplitude constant : ℝ}
    (hupper :
      ∀ point, point ∈ directionalBlowUpChamber →
        forwardBlowUpSq amplitude point ≤ constant)
    (first second : AmbientPlane) :
    dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second) ^ 2 ≤
      constant * dist first second ^ 2 := by
  by_cases hsame : first = second
  · subst second
    simp
  · rw [chordBlowUp_forward_sq_identity amplitude hsame]
    exact mul_le_mul_of_nonneg_right
      (hupper (chordBlowUp first second)
        (chordBlowUp_mem_chamber hsame))
      (sq_nonneg (dist first second))

theorem exists_finite_forwardChordSqCertificate
    {amplitude delta : ℝ}
    (ha : 0 ≤ amplitude) (hdelta : 0 < delta) :
    ∃ sample : List (NoisyUpperReading BlowUpPoint),
      NoisyUpperSampleValid (forwardBlowUpSq amplitude) sample ∧
        DeltaCoverage directionalBlowUpChamber sample delta ∧
          SampleInside directionalBlowUpChamber sample ∧
            RegularityCertificate directionalBlowUpChamber sample
              (forwardBlowUpSqRegularity amplitude)
              (forwardBlowUpSq amplitude) ∧
              ∀ first second : AmbientPlane,
                dist (intrinsicShearMap amplitude first)
                    (intrinsicShearMap amplitude second) ^ 2 ≤
                  (noisySampleUpper sample +
                    forwardBlowUpSqRegularity amplitude * delta) *
                    dist first second ^ 2 := by
  rcases exists_forwardBlowUpSq_finiteCertificate ha hdelta with
    ⟨sample, hvalid, hcoverage, hinside, hregular, hglobal⟩
  refine ⟨sample, hvalid, hcoverage, hinside, hregular, ?_⟩
  intro first second
  exact chord_sq_bound_of_blowUp_upper hglobal first second

end BoundaryOfSelf.IntrinsicNonradialShearDiagonalBlowUp
