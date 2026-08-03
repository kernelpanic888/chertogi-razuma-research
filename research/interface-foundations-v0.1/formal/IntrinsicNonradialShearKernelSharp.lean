import IntrinsicNonradialShearExactSupport

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearKernelSharp

open LocalSegmentRealCompletion
open StandardHausdorffMetricBridge
open OneSidedEuclideanContourBound
open CompactTentHomeomorphism
open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearExactSupport

def kernelOrigin : AmbientPlane :=
  planeEmbedding ({ x := 0, y := 0 } : RealPlanePoint)

def kernelDiagonalPoint (t : ℝ) : AmbientPlane :=
  planeEmbedding ({ x := -t, y := -t } : RealPlanePoint)

lemma shearKernel_kernelOrigin : shearKernel kernelOrigin = 1 := by
  simp [kernelOrigin, shearKernel, planeEmbedding, tentBump]

lemma shearKernel_kernelDiagonalPoint
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    shearKernel (kernelDiagonalPoint t) = (1 - t) ^ 2 := by
  simp [kernelDiagonalPoint, shearKernel, planeEmbedding, tentBump,
    abs_of_nonneg ht0, ht1]
  ring

lemma dist_kernelOrigin_kernelDiagonalPoint
    {t : ℝ} (ht0 : 0 ≤ t) :
    dist kernelOrigin (kernelDiagonalPoint t) = Real.sqrt 2 * t := by
  rw [show kernelOrigin = planeEmbedding ({ x := 0, y := 0 } : RealPlanePoint) by rfl]
  rw [show kernelDiagonalPoint t = planeEmbedding ({ x := -t, y := -t } : RealPlanePoint) by rfl]
  rw [dist_planeEmbedding_eq_euclideanDistance]
  simp [euclideanDistance, squaredDistance]
  rw [show t ^ 2 + t ^ 2 = 2 * t ^ 2 by ring]
  rw [Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ))]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht0]

def KernelMetricBound (constant : ℝ) : Prop :=
  ∀ first second : AmbientPlane,
    |shearKernel first - shearKernel second| ≤ constant * dist first second

theorem sqrt_two_is_kernel_metric_bound :
    KernelMetricBound (Real.sqrt 2) := by
  intro first second
  exact shearKernel_abs_sub_le_sqrt_two first second

lemma diagonal_defeats_smaller_kernel_constant
    {constant : ℝ} (hc0 : 0 ≤ constant) (hc : constant < Real.sqrt 2) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      constant * dist kernelOrigin (kernelDiagonalPoint t) <
        |shearKernel kernelOrigin - shearKernel (kernelDiagonalPoint t)| := by
  let s : ℝ := Real.sqrt 2
  let t : ℝ := (2 - constant * s) / 2
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 2
  have hs : 0 < s := Real.sqrt_pos.2 (by norm_num)
  have hs2 : s ^ 2 = 2 := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hcs : constant * s < 2 := by
    have := mul_lt_mul_of_pos_right hc hs
    nlinarith
  have ht0 : 0 < t := by
    dsimp [t]
    nlinarith
  have ht1 : t ≤ 1 := by
    dsimp [t]
    nlinarith
  refine ⟨t, ht0, ht1, ?_⟩
  rw [dist_kernelOrigin_kernelDiagonalPoint (le_of_lt ht0)]
  rw [shearKernel_kernelOrigin]
  rw [shearKernel_kernelDiagonalPoint (le_of_lt ht0) ht1]
  have habs : 0 ≤ 1 - (1 - t) ^ 2 := by
    nlinarith
  rw [abs_of_nonneg habs]
  change constant * (s * t) < 1 - (1 - t) ^ 2
  dsimp [t]
  nlinarith

theorem kernel_metric_bound_ge_sqrt_two
    {constant : ℝ} (hc0 : 0 ≤ constant) (hbound : KernelMetricBound constant) :
    Real.sqrt 2 ≤ constant := by
  by_contra hnot
  have hc : constant < Real.sqrt 2 := lt_of_not_ge hnot
  obtain ⟨t, _ht0, _ht1, hstrict⟩ :=
    diagonal_defeats_smaller_kernel_constant hc0 hc
  have hupper := hbound kernelOrigin (kernelDiagonalPoint t)
  linarith

theorem kernel_metric_bound_iff
    {constant : ℝ} (hc0 : 0 ≤ constant) :
    KernelMetricBound constant ↔ Real.sqrt 2 ≤ constant := by
  constructor
  · exact kernel_metric_bound_ge_sqrt_two hc0
  · intro hc first second
    calc
      |shearKernel first - shearKernel second|
          ≤ Real.sqrt 2 * dist first second :=
            shearKernel_abs_sub_le_sqrt_two first second
      _ ≤ constant * dist first second := by
        exact mul_le_mul_of_nonneg_right hc dist_nonneg

noncomputable def forwardSpectralSq (amplitude : ℝ) : ℝ :=
  1 + amplitude + amplitude ^ 2 +
    amplitude * Real.sqrt (amplitude ^ 2 + 2 * amplitude + 2)

theorem forward_spectral_quadratic_bound
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (x y : ℝ) :
    x ^ 2 + (amplitude * x + (1 + amplitude) * y) ^ 2 ≤
      forwardSpectralSq amplitude * (x ^ 2 + y ^ 2) := by
  by_cases ha0 : amplitude = 0
  · subst amplitude
    simp [forwardSpectralSq]
  · have haPos : 0 < amplitude := lt_of_le_of_ne ha (Ne.symm ha0)
    let r : ℝ := Real.sqrt (amplitude ^ 2 + 2 * amplitude + 2)
    let lambda : ℝ := forwardSpectralSq amplitude
    let A : ℝ := lambda - (1 + amplitude ^ 2)
    let B : ℝ := amplitude * (1 + amplitude)
    let C : ℝ := lambda - (1 + amplitude) ^ 2
    let gap : ℝ :=
      lambda * (x ^ 2 + y ^ 2) -
        (x ^ 2 + (amplitude * x + (1 + amplitude) * y) ^ 2)
    have hrad : 0 ≤ amplitude ^ 2 + 2 * amplitude + 2 := by nlinarith
    have hr0 : 0 ≤ r := by
      dsimp [r]
      exact Real.sqrt_nonneg _
    have hr2 : r ^ 2 = amplitude ^ 2 + 2 * amplitude + 2 := by
      dsimp [r]
      exact Real.sq_sqrt hrad
    have hr1 : 1 ≤ r := by nlinarith [sq_nonneg (r - 1)]
    have hA : A = amplitude * (1 + r) := by
      dsimp [A, lambda, forwardSpectralSq, r]
      ring
    have hC : C = amplitude * (r - 1) := by
      dsimp [C, lambda, forwardSpectralSq, r]
      ring
    have hB : B = amplitude * (1 + amplitude) := rfl
    have hApos : 0 < A := by rw [hA]; positivity
    have hAC : A * C = B ^ 2 := by
      rw [hA, hC, hB]
      nlinarith
    have hgap : gap = A * x ^ 2 - 2 * B * x * y + C * y ^ 2 := by
      dsimp [gap, A, B, C, lambda, forwardSpectralSq]
      ring
    have hfactor : A * gap = (A * x - B * y) ^ 2 := by
      rw [hgap]
      calc
        A * (A * x ^ 2 - 2 * B * x * y + C * y ^ 2) =
            (A * x) ^ 2 - 2 * A * B * x * y + (A * C) * y ^ 2 := by ring
        _ = (A * x) ^ 2 - 2 * A * B * x * y + B ^ 2 * y ^ 2 := by rw [hAC]
        _ = (A * x - B * y) ^ 2 := by ring
    have hgap0 : 0 ≤ gap := by
      by_contra hneg
      have hmul : A * gap < 0 := mul_neg_of_pos_of_neg hApos (lt_of_not_ge hneg)
      rw [hfactor] at hmul
      exact (not_lt_of_ge (sq_nonneg (A * x - B * y))) hmul
    dsimp [gap, lambda] at hgap0
    linarith

theorem forward_spectral_sq_nonneg
    {amplitude : ℝ} (ha : 0 ≤ amplitude) :
    0 ≤ forwardSpectralSq amplitude := by
  have h := forward_spectral_quadratic_bound ha 1 0
  norm_num at h
  nlinarith [sq_nonneg amplitude]

def ForwardQuadraticBound (amplitude constant : ℝ) : Prop :=
  ∀ x y : ℝ,
    x ^ 2 + (amplitude * x + (1 + amplitude) * y) ^ 2 ≤
      constant * (x ^ 2 + y ^ 2)

theorem forward_spectral_sq_is_quadratic_bound
    {amplitude : ℝ} (ha : 0 ≤ amplitude) :
    ForwardQuadraticBound amplitude (forwardSpectralSq amplitude) := by
  exact forward_spectral_quadratic_bound ha

theorem forward_quadratic_bound_ge_spectral_sq
    {amplitude constant : ℝ} (ha : 0 ≤ amplitude)
    (hbound : ForwardQuadraticBound amplitude constant) :
    forwardSpectralSq amplitude ≤ constant := by
  by_cases ha0 : amplitude = 0
  · subst amplitude
    have h := hbound 1 0
    norm_num [ForwardQuadraticBound, forwardSpectralSq] at h ⊢
    exact h
  · have haPos : 0 < amplitude := lt_of_le_of_ne ha (Ne.symm ha0)
    let r : ℝ := Real.sqrt (amplitude ^ 2 + 2 * amplitude + 2)
    let lambda : ℝ := forwardSpectralSq amplitude
    let A : ℝ := amplitude * (1 + r)
    let B : ℝ := amplitude * (1 + amplitude)
    let C : ℝ := amplitude * (r - 1)
    have hrad : 0 ≤ amplitude ^ 2 + 2 * amplitude + 2 := by nlinarith
    have hr2 : r ^ 2 = amplitude ^ 2 + 2 * amplitude + 2 := by
      dsimp [r]
      exact Real.sq_sqrt hrad
    have hApos : 0 < A := by
      dsimp [A]
      have : 0 ≤ r := by dsimp [r]; exact Real.sqrt_nonneg _
      positivity
    have hlambdaA : lambda - (1 + amplitude ^ 2) = A := by
      dsimp [lambda, A, forwardSpectralSq, r]
      ring
    have hlambdaC : lambda - (1 + amplitude) ^ 2 = C := by
      dsimp [lambda, C, forwardSpectralSq, r]
      ring
    have hAC : A * C = B ^ 2 := by
      dsimp [A, B, C]
      calc
        (amplitude * (1 + r)) * (amplitude * (r - 1)) =
            amplitude ^ 2 * (r ^ 2 - 1) := by ring
        _ = (amplitude * (1 + amplitude)) ^ 2 := by rw [hr2]; ring
    have hnorm : 0 < B ^ 2 + A ^ 2 := by nlinarith [sq_pos_of_pos hApos]
    have hfirst :
        (1 + amplitude ^ 2) * B + B * A = lambda * B := by
      nlinarith
    have hsecond :
        B * B + (1 + amplitude) ^ 2 * A = lambda * A := by
      nlinarith
    have heigen :
        B ^ 2 + (amplitude * B + (1 + amplitude) * A) ^ 2 =
          forwardSpectralSq amplitude * (B ^ 2 + A ^ 2) := by
      change
        B ^ 2 + (amplitude * B + (1 + amplitude) * A) ^ 2 =
          lambda * (B ^ 2 + A ^ 2)
      calc
        B ^ 2 + (amplitude * B + (1 + amplitude) * A) ^ 2 =
            B * ((1 + amplitude ^ 2) * B + B * A) +
              A * (B * B + (1 + amplitude) ^ 2 * A) := by
                dsimp [B]
                ring
        _ = B * (lambda * B) + A * (lambda * A) := by rw [hfirst, hsecond]
        _ = lambda * (B ^ 2 + A ^ 2) := by ring
    have h := hbound B A
    rw [heigen] at h
    nlinarith

theorem forward_quadratic_bound_iff
    {amplitude constant : ℝ} (ha : 0 ≤ amplitude) :
    ForwardQuadraticBound amplitude constant ↔
      forwardSpectralSq amplitude ≤ constant := by
  constructor
  · exact forward_quadratic_bound_ge_spectral_sq ha
  · intro hc x y
    calc
      x ^ 2 + (amplitude * x + (1 + amplitude) * y) ^ 2
          ≤ forwardSpectralSq amplitude * (x ^ 2 + y ^ 2) :=
            forward_spectral_quadratic_bound ha x y
      _ ≤ constant * (x ^ 2 + y ^ 2) := by
        exact mul_le_mul_of_nonneg_right hc (by positivity)

end BoundaryOfSelf.IntrinsicNonradialShearKernelSharp
