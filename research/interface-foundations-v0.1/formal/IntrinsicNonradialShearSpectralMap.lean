import IntrinsicNonradialShearKernelSharp

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearSpectralMap

open StandardHausdorffMetricBridge
open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearExactSupport
open IntrinsicNonradialShearKernelSharp

lemma intrinsicShearMap_dist_sq_eq
    (amplitude : ℝ) (first second : AmbientPlane) :
    dist (intrinsicShearMap amplitude first) (intrinsicShearMap amplitude second) ^ 2 =
      (first.ofLp 0 - second.ofLp 0) ^ 2 +
      ((first.ofLp 1 - second.ofLp 1) +
        amplitude * (shearKernel first - shearKernel second)) ^ 2 := by
  rw [dist_sq_eq_coordinate_sq_sum]
  simp [intrinsicShearMap, planeEmbedding]
  ring

lemma intrinsicShear_vertical_difference_abs_le
    {amplitude : ℝ} (ha : 0 ≤ amplitude)
    (first second : AmbientPlane) :
    |(first.ofLp 1 - second.ofLp 1) +
        amplitude * (shearKernel first - shearKernel second)| ≤
      amplitude * |first.ofLp 0 - second.ofLp 0| +
        (1 + amplitude) * |first.ofLp 1 - second.ofLp 1| := by
  have hkernel := shearKernel_abs_sub_le_coordinate_sum first second
  calc
    |(first.ofLp 1 - second.ofLp 1) +
        amplitude * (shearKernel first - shearKernel second)|
        ≤ |first.ofLp 1 - second.ofLp 1| +
            |amplitude * (shearKernel first - shearKernel second)| := abs_add_le _ _
    _ = |first.ofLp 1 - second.ofLp 1| +
          amplitude * |shearKernel first - shearKernel second| := by
            rw [abs_mul, abs_of_nonneg ha]
    _ ≤ |first.ofLp 1 - second.ofLp 1| +
          amplitude * (|first.ofLp 0 - second.ofLp 0| +
            |first.ofLp 1 - second.ofLp 1|) := by
              have hmul := mul_le_mul_of_nonneg_left hkernel ha
              linarith
    _ = amplitude * |first.ofLp 0 - second.ofLp 0| +
          (1 + amplitude) * |first.ofLp 1 - second.ofLp 1| := by ring

theorem intrinsicShearMap_dist_sq_le_forwardSpectralSq
    {amplitude : ℝ} (ha : 0 ≤ amplitude)
    (first second : AmbientPlane) :
    dist (intrinsicShearMap amplitude first) (intrinsicShearMap amplitude second) ^ 2 ≤
      forwardSpectralSq amplitude * dist first second ^ 2 := by
  let dx : ℝ := first.ofLp 0 - second.ofLp 0
  let dy : ℝ := first.ofLp 1 - second.ofLp 1
  let dk : ℝ := shearKernel first - shearKernel second
  let vertical : ℝ := dy + amplitude * dk
  let envelope : ℝ := amplitude * |dx| + (1 + amplitude) * |dy|
  have hvertical : |vertical| ≤ envelope := by
    dsimp [vertical, envelope, dx, dy, dk]
    exact intrinsicShear_vertical_difference_abs_le ha first second
  have henvelope0 : 0 ≤ envelope := by
    dsimp [envelope]
    positivity
  have hverticalSq : vertical ^ 2 ≤ envelope ^ 2 := by
    have habs0 : 0 ≤ |vertical| := abs_nonneg _
    have hmul := mul_self_le_mul_self habs0 hvertical
    simpa [pow_two] using hmul
  have hquad := forward_spectral_quadratic_bound ha |dx| |dy|
  have hchain :
      dx ^ 2 + vertical ^ 2 ≤
        forwardSpectralSq amplitude * (dx ^ 2 + dy ^ 2) := by
    calc
      dx ^ 2 + vertical ^ 2 ≤ dx ^ 2 + envelope ^ 2 := by linarith
      _ = |dx| ^ 2 +
          (amplitude * |dx| + (1 + amplitude) * |dy|) ^ 2 := by
            dsimp [envelope]
            rw [sq_abs]
      _ ≤ forwardSpectralSq amplitude * (|dx| ^ 2 + |dy| ^ 2) := hquad
      _ = forwardSpectralSq amplitude * (dx ^ 2 + dy ^ 2) := by
            rw [sq_abs, sq_abs]
  rw [intrinsicShearMap_dist_sq_eq]
  rw [dist_sq_eq_coordinate_sq_sum]
  exact hchain

noncomputable def forwardSpectralConstant (amplitude : ℝ) : ℝ :=
  Real.sqrt (forwardSpectralSq amplitude)

theorem intrinsicShearMap_dist_le_forwardSpectralConstant
    {amplitude : ℝ} (ha : 0 ≤ amplitude)
    (first second : AmbientPlane) :
    dist (intrinsicShearMap amplitude first) (intrinsicShearMap amplitude second) ≤
      forwardSpectralConstant amplitude * dist first second := by
  have hspectral0 := forward_spectral_sq_nonneg ha
  have hsquare :=
    intrinsicShearMap_dist_sq_le_forwardSpectralSq ha first second
  have hconstant0 : 0 ≤ forwardSpectralConstant amplitude := by
    exact Real.sqrt_nonneg _
  have hconstantSq :
      forwardSpectralConstant amplitude ^ 2 = forwardSpectralSq amplitude := by
    dsimp [forwardSpectralConstant]
    exact Real.sq_sqrt hspectral0
  have hright0 :
      0 ≤ forwardSpectralConstant amplitude * dist first second :=
    mul_nonneg hconstant0 dist_nonneg
  have hsquare' :
      dist (intrinsicShearMap amplitude first) (intrinsicShearMap amplitude second) ^ 2 ≤
        (forwardSpectralConstant amplitude * dist first second) ^ 2 := by
    rw [mul_pow, hconstantSq]
    exact hsquare
  nlinarith [dist_nonneg (x :=
    intrinsicShearMap amplitude first) (y := intrinsicShearMap amplitude second)]

def kernelDirectionalPoint (t x y : ℝ) : AmbientPlane :=
  planeEmbedding
    ({ x := -(t * x), y := -(t * y) } :
      LocalSegmentRealCompletion.RealPlanePoint)

lemma shearKernel_kernelDirectionalPoint
    {t x y : ℝ}
    (htx0 : 0 ≤ t * x) (htx1 : t * x ≤ 1)
    (hty0 : 0 ≤ t * y) (hty1 : t * y ≤ 1) :
    shearKernel (kernelDirectionalPoint t x y) =
      (1 - t * x) * (1 - t * y) := by
  simp [kernelDirectionalPoint, shearKernel, planeEmbedding,
    CompactTentHomeomorphism.tentBump, abs_of_nonneg htx0,
    abs_of_nonneg hty0, htx1, hty1]

lemma dist_kernelOrigin_kernelDirectionalPoint_sq
    (t x y : ℝ) :
    dist IntrinsicNonradialShearKernelSharp.kernelOrigin
      (kernelDirectionalPoint t x y) ^ 2 =
        (t * x) ^ 2 + (t * y) ^ 2 := by
  rw [dist_sq_eq_coordinate_sq_sum]
  simp [IntrinsicNonradialShearKernelSharp.kernelOrigin,
    kernelDirectionalPoint, planeEmbedding]

lemma intrinsicShearMap_kernelDirectionalPoint_sq
    {amplitude t x y : ℝ}
    (htx0 : 0 ≤ t * x) (htx1 : t * x ≤ 1)
    (hty0 : 0 ≤ t * y) (hty1 : t * y ≤ 1) :
    dist
      (intrinsicShearMap amplitude
        IntrinsicNonradialShearKernelSharp.kernelOrigin)
      (intrinsicShearMap amplitude (kernelDirectionalPoint t x y)) ^ 2 =
        (t * x) ^ 2 +
          (t * y + amplitude *
            (1 - (1 - t * x) * (1 - t * y))) ^ 2 := by
  rw [intrinsicShearMap_dist_sq_eq]
  rw [IntrinsicNonradialShearKernelSharp.shearKernel_kernelOrigin]
  rw [shearKernel_kernelDirectionalPoint htx0 htx1 hty0 hty1]
  simp [IntrinsicNonradialShearKernelSharp.kernelOrigin,
    kernelDirectionalPoint, planeEmbedding]

noncomputable def spectralRoot (amplitude : ℝ) : ℝ :=
  Real.sqrt (amplitude ^ 2 + 2 * amplitude + 2)

noncomputable def spectralHorizontal (amplitude : ℝ) : ℝ :=
  amplitude * (1 + amplitude)

noncomputable def spectralVertical (amplitude : ℝ) : ℝ :=
  amplitude * (1 + spectralRoot amplitude)

noncomputable def spectralOutputVertical (amplitude : ℝ) : ℝ :=
  amplitude * spectralHorizontal amplitude +
    (1 + amplitude) * spectralVertical amplitude

lemma spectral_eigenvector_identity
    {amplitude : ℝ} (ha : 0 < amplitude) :
    spectralHorizontal amplitude ^ 2 +
        spectralOutputVertical amplitude ^ 2 =
      forwardSpectralSq amplitude *
        (spectralHorizontal amplitude ^ 2 +
          spectralVertical amplitude ^ 2) := by
  let r : ℝ := spectralRoot amplitude
  let A : ℝ := spectralVertical amplitude
  let B : ℝ := spectralHorizontal amplitude
  let V : ℝ := spectralOutputVertical amplitude
  let lambda : ℝ := forwardSpectralSq amplitude
  let C : ℝ := amplitude * (r - 1)
  have hrad : 0 ≤ amplitude ^ 2 + 2 * amplitude + 2 := by nlinarith
  have hr2 : r ^ 2 = amplitude ^ 2 + 2 * amplitude + 2 := by
    dsimp [r, spectralRoot]
    exact Real.sq_sqrt hrad
  have hlambdaA : lambda - (1 + amplitude ^ 2) = A := by
    dsimp [lambda, A, forwardSpectralSq, spectralVertical, spectralRoot, r]
    ring
  have hlambdaC : lambda - (1 + amplitude) ^ 2 = C := by
    dsimp [lambda, C, forwardSpectralSq, spectralRoot, r]
    ring
  have hAC : A * C = B ^ 2 := by
    dsimp [A, B, C, spectralVertical, spectralHorizontal]
    calc
      (amplitude * (1 + r)) * (amplitude * (r - 1)) =
          amplitude ^ 2 * (r ^ 2 - 1) := by ring
      _ = (amplitude * (1 + amplitude)) ^ 2 := by rw [hr2]; ring
  have hfirst :
      (1 + amplitude ^ 2) * B + B * A = lambda * B := by
    rw [← hlambdaA]
    ring
  have hsecond :
      B * B + (1 + amplitude) ^ 2 * A = lambda * A := by
    have hBB : B * B = A * C := by
      calc
        B * B = B ^ 2 := by ring
        _ = A * C := hAC.symm
    have hsum : C + (1 + amplitude) ^ 2 = lambda := by linarith
    rw [hBB]
    calc
      A * C + (1 + amplitude) ^ 2 * A =
          A * (C + (1 + amplitude) ^ 2) := by ring
      _ = A * lambda := by rw [hsum]
      _ = lambda * A := by ring
  change B ^ 2 + V ^ 2 = lambda * (B ^ 2 + A ^ 2)
  have hV : V = amplitude * B + (1 + amplitude) * A := by
    rfl
  rw [hV]
  calc
    B ^ 2 + (amplitude * B + (1 + amplitude) * A) ^ 2 =
        B * ((1 + amplitude ^ 2) * B + B * A) +
          A * (B * B + (1 + amplitude) ^ 2 * A) := by
            dsimp [B, spectralHorizontal]
            ring
    _ = B * (lambda * B) + A * (lambda * A) := by rw [hfirst, hsecond]
    _ = lambda * (B ^ 2 + A ^ 2) := by ring

def ForwardMapMetricBound (amplitude constant : ℝ) : Prop :=
  ∀ first second : AmbientPlane,
    dist (intrinsicShearMap amplitude first) (intrinsicShearMap amplitude second) ≤
      constant * dist first second

theorem forwardSpectralConstant_is_map_metric_bound
    {amplitude : ℝ} (ha : 0 ≤ amplitude) :
    ForwardMapMetricBound amplitude (forwardSpectralConstant amplitude) := by
  exact intrinsicShearMap_dist_le_forwardSpectralConstant ha

lemma forward_map_metric_bound_ge_one_at_zero
    {constant : ℝ} (hbound : ForwardMapMetricBound 0 constant) :
    1 ≤ constant := by
  let point := kernelDirectionalPoint 1 1 0
  have hdistSq :
      dist IntrinsicNonradialShearKernelSharp.kernelOrigin point ^ 2 = 1 := by
    dsimp [point]
    rw [dist_kernelOrigin_kernelDirectionalPoint_sq]
    norm_num
  have hdist : dist IntrinsicNonradialShearKernelSharp.kernelOrigin point = 1 := by
    have hnonneg :
        0 ≤ dist IntrinsicNonradialShearKernelSharp.kernelOrigin point :=
      dist_nonneg
    nlinarith
  have houtputSq :
      dist
          (intrinsicShearMap 0
            IntrinsicNonradialShearKernelSharp.kernelOrigin)
          (intrinsicShearMap 0 point) ^ 2 = 1 := by
    dsimp [point]
    rw [intrinsicShearMap_kernelDirectionalPoint_sq
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have houtput :
      dist
          (intrinsicShearMap 0
            IntrinsicNonradialShearKernelSharp.kernelOrigin)
          (intrinsicShearMap 0 point) = 1 := by
    have hnonneg :
        0 ≤ dist
          (intrinsicShearMap 0
            IntrinsicNonradialShearKernelSharp.kernelOrigin)
          (intrinsicShearMap 0 point) :=
      dist_nonneg
    nlinarith
  have h := hbound IntrinsicNonradialShearKernelSharp.kernelOrigin point
  rw [houtput, hdist] at h
  simpa using h

theorem forward_map_metric_bound_ge_spectralConstant
    {amplitude constant : ℝ} (ha : 0 ≤ amplitude) (hc : 0 ≤ constant)
    (hbound : ForwardMapMetricBound amplitude constant) :
    forwardSpectralConstant amplitude ≤ constant := by
  by_cases ha0 : amplitude = 0
  · subst amplitude
    have hOne := forward_map_metric_bound_ge_one_at_zero hbound
    norm_num [forwardSpectralConstant, forwardSpectralSq]
    exact hOne
  · have haPos : 0 < amplitude := lt_of_le_of_ne ha (Ne.symm ha0)
    let B : ℝ := spectralHorizontal amplitude
    let A : ℝ := spectralVertical amplitude
    let V : ℝ := spectralOutputVertical amplitude
    let lambda : ℝ := forwardSpectralSq amplitude
    let L : ℝ := forwardSpectralConstant amplitude
    have hr0 : 0 ≤ spectralRoot amplitude := by
      dsimp [spectralRoot]
      exact Real.sqrt_nonneg _
    have hB : 0 < B := by
      dsimp [B, spectralHorizontal]
      positivity
    have hA : 0 < A := by
      dsimp [A, spectralVertical]
      positivity
    have hV : 0 < V := by
      dsimp [V, spectralOutputVertical]
      positivity
    have hN : 0 < B ^ 2 + A ^ 2 := by nlinarith [sq_pos_of_pos hA]
    have hlambda0 : 0 ≤ lambda := by
      dsimp [lambda]
      exact forward_spectral_sq_nonneg ha
    have hL0 : 0 ≤ L := by
      dsimp [L, forwardSpectralConstant]
      exact Real.sqrt_nonneg _
    have hL2 : L ^ 2 = lambda := by
      dsimp [L, forwardSpectralConstant, lambda]
      exact Real.sq_sqrt hlambda0
    by_contra hnot
    have hcL : constant < L := lt_of_not_ge hnot
    have hc2 : constant ^ 2 < lambda := by nlinarith
    let delta : ℝ := lambda - constant ^ 2
    let N : ℝ := B ^ 2 + A ^ 2
    let K : ℝ := 2 * V * amplitude * A * B
    let D : ℝ := delta * N + K + delta * N * A + delta * N * B
    let t : ℝ := delta * N / D
    have hdelta : 0 < delta := by dsimp [delta]; linarith
    have hK : 0 < K := by dsimp [K]; positivity
    have hD : 0 < D := by dsimp [D]; positivity
    have ht : 0 < t := by dsimp [t]; positivity
    have htA : t * A ≤ 1 := by
      rw [show t * A = (delta * N * A) / D by dsimp [t]; ring]
      apply (div_le_iff₀ hD).2
      dsimp [D]
      nlinarith [mul_pos hdelta hN, mul_pos (mul_pos hdelta hN) hA]
    have htB : t * B ≤ 1 := by
      rw [show t * B = (delta * N * B) / D by dsimp [t]; ring]
      apply (div_le_iff₀ hD).2
      dsimp [D]
      nlinarith [mul_pos hdelta hN, mul_pos (mul_pos hdelta hN) hB]
    have hKt : K * t < delta * N := by
      have hKD : K < D := by
        dsimp [D]
        nlinarith [mul_pos hdelta hN]
      have hmul := mul_lt_mul_of_pos_left hKD (mul_pos hdelta hN)
      rw [show K * t = (K * (delta * N)) / D by dsimp [t]; ring]
      apply (div_lt_iff₀ hD).2
      nlinarith
    let probe : AmbientPlane := kernelDirectionalPoint t B A
    have hinput :
        dist IntrinsicNonradialShearKernelSharp.kernelOrigin probe ^ 2 =
          t ^ 2 * N := by
      dsimp [probe, N]
      rw [dist_kernelOrigin_kernelDirectionalPoint_sq]
      ring
    have houtput :
        dist
          (intrinsicShearMap amplitude
            IntrinsicNonradialShearKernelSharp.kernelOrigin)
          (intrinsicShearMap amplitude probe) ^ 2 =
            t ^ 2 * (B ^ 2 + (V - amplitude * t * A * B) ^ 2) := by
      dsimp [probe]
      rw [intrinsicShearMap_kernelDirectionalPoint_sq
        (mul_nonneg (le_of_lt ht) (le_of_lt hB)) htB
        (mul_nonneg (le_of_lt ht) (le_of_lt hA)) htA]
      change
        (t * B) ^ 2 +
            (t * A + amplitude *
              (1 - (1 - t * B) * (1 - t * A))) ^ 2 =
          t ^ 2 * (B ^ 2 + (V - amplitude * t * A * B) ^ 2)
      have hVdef : V = amplitude * B + (1 + amplitude) * A := rfl
      rw [hVdef]
      ring
    have heigen :
        B ^ 2 + V ^ 2 = lambda * N := by
      dsimp [B, A, V, lambda, N]
      exact spectral_eigenvector_identity haPos
    have hstrictCore :
        constant ^ 2 * N <
          B ^ 2 + (V - amplitude * t * A * B) ^ 2 := by
      dsimp [K] at hKt
      dsimp [delta] at hdelta
      nlinarith [sq_nonneg (amplitude * t * A * B)]
    have hstrictSq :
        constant ^ 2 *
            dist IntrinsicNonradialShearKernelSharp.kernelOrigin probe ^ 2 <
          dist
            (intrinsicShearMap amplitude
              IntrinsicNonradialShearKernelSharp.kernelOrigin)
            (intrinsicShearMap amplitude probe) ^ 2 := by
      rw [hinput, houtput]
      have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
      nlinarith
    have hmetric :=
      hbound IntrinsicNonradialShearKernelSharp.kernelOrigin probe
    have hmetricSq :
        dist
            (intrinsicShearMap amplitude
              IntrinsicNonradialShearKernelSharp.kernelOrigin)
            (intrinsicShearMap amplitude probe) ^ 2 ≤
          constant ^ 2 *
            dist IntrinsicNonradialShearKernelSharp.kernelOrigin probe ^ 2 := by
      have hmul := mul_self_le_mul_self
        (dist_nonneg :
          0 ≤ dist
            (intrinsicShearMap amplitude
              IntrinsicNonradialShearKernelSharp.kernelOrigin)
            (intrinsicShearMap amplitude probe))
        hmetric
      nlinarith
    linarith

theorem forward_map_metric_bound_iff
    {amplitude constant : ℝ} (ha : 0 ≤ amplitude) (hc : 0 ≤ constant) :
    ForwardMapMetricBound amplitude constant ↔
      forwardSpectralConstant amplitude ≤ constant := by
  constructor
  · exact forward_map_metric_bound_ge_spectralConstant ha hc
  · intro hconstant first second
    calc
      dist (intrinsicShearMap amplitude first) (intrinsicShearMap amplitude second)
          ≤ forwardSpectralConstant amplitude * dist first second :=
            intrinsicShearMap_dist_le_forwardSpectralConstant ha first second
      _ ≤ constant * dist first second :=
        mul_le_mul_of_nonneg_right hconstant dist_nonneg

noncomputable def inverseSpectralParameter (amplitude : ℝ) : ℝ :=
  amplitude / (1 - amplitude)

noncomputable def inverseSpectralSq (amplitude : ℝ) : ℝ :=
  forwardSpectralSq (inverseSpectralParameter amplitude)

noncomputable def inverseSpectralConstant (amplitude : ℝ) : ℝ :=
  Real.sqrt (inverseSpectralSq amplitude)

lemma inverseSpectralSq_closed_form
    {amplitude : ℝ} (ha1 : amplitude < 1) :
    inverseSpectralSq amplitude =
      (1 - amplitude + amplitude ^ 2 +
        amplitude * Real.sqrt (amplitude ^ 2 - 2 * amplitude + 2)) /
          (1 - amplitude) ^ 2 := by
  have hden : 0 < 1 - amplitude := by linarith
  have hdenNe : 1 - amplitude ≠ 0 := ne_of_gt hden
  have hrad : 0 ≤ amplitude ^ 2 - 2 * amplitude + 2 := by
    nlinarith [sq_nonneg (amplitude - 1)]
  have hinside :
      inverseSpectralParameter amplitude ^ 2 +
          2 * inverseSpectralParameter amplitude + 2 =
        (amplitude ^ 2 - 2 * amplitude + 2) /
          (1 - amplitude) ^ 2 := by
    dsimp [inverseSpectralParameter]
    field_simp [hdenNe]
    ring
  have hsqrt :
      Real.sqrt
          (inverseSpectralParameter amplitude ^ 2 +
            2 * inverseSpectralParameter amplitude + 2) =
        Real.sqrt (amplitude ^ 2 - 2 * amplitude + 2) /
          (1 - amplitude) := by
    rw [hinside, Real.sqrt_div hrad]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hden]
  dsimp [inverseSpectralSq, forwardSpectralSq]
  rw [hsqrt]
  dsimp [inverseSpectralParameter]
  field_simp [hdenNe]
  ring

lemma inverseSpectralParameter_nonneg
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    0 ≤ inverseSpectralParameter amplitude := by
  dsimp [inverseSpectralParameter]
  positivity

lemma one_add_inverseSpectralParameter
    {amplitude : ℝ} (ha1 : amplitude < 1) :
    1 + inverseSpectralParameter amplitude = 1 / (1 - amplitude) := by
  dsimp [inverseSpectralParameter]
  have hne : 1 - amplitude ≠ 0 := by linarith
  field_simp [hne]
  ring

lemma intrinsicShear_input_vertical_abs_le_inverseEnvelope
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (ha1 : amplitude < 1)
    (first second : AmbientPlane) :
    |first.ofLp 1 - second.ofLp 1| ≤
      inverseSpectralParameter amplitude *
          |first.ofLp 0 - second.ofLp 0| +
        (1 + inverseSpectralParameter amplitude) *
          |(first.ofLp 1 - second.ofLp 1) +
            amplitude * (shearKernel first - shearKernel second)| := by
  let dx : ℝ := first.ofLp 0 - second.ofLp 0
  let dy : ℝ := first.ofLp 1 - second.ofLp 1
  let dk : ℝ := shearKernel first - shearKernel second
  let vertical : ℝ := dy + amplitude * dk
  have hkernel := shearKernel_abs_sub_le_coordinate_sum first second
  have hdy :
      |dy| ≤ |vertical| + amplitude * |dk| := by
    have hrewrite : dy = vertical - amplitude * dk := by
      dsimp [vertical]
      ring
    rw [hrewrite]
    calc
      |vertical - amplitude * dk| ≤ |vertical| + |amplitude * dk| :=
        abs_sub _ _
      _ = |vertical| + amplitude * |dk| := by
        rw [abs_mul, abs_of_nonneg ha]
  have hlinear :
      (1 - amplitude) * |dy| ≤ |vertical| + amplitude * |dx| := by
    have hmul := mul_le_mul_of_nonneg_left hkernel ha
    nlinarith
  have hden : 0 < 1 - amplitude := by linarith
  have hrearrange :
      inverseSpectralParameter amplitude * |dx| +
          (1 + inverseSpectralParameter amplitude) * |vertical| =
        (amplitude * |dx| + |vertical|) / (1 - amplitude) := by
    dsimp [inverseSpectralParameter]
    field_simp
    ring
  dsimp [dx, dy, dk, vertical] at *
  rw [hrearrange]
  apply (le_div_iff₀ hden).2
  nlinarith

theorem intrinsicShearMap_colipschitz_sq_inverseSpectralSq
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (ha1 : amplitude < 1)
    (first second : AmbientPlane) :
    dist first second ^ 2 ≤
      inverseSpectralSq amplitude *
        dist (intrinsicShearMap amplitude first)
          (intrinsicShearMap amplitude second) ^ 2 := by
  let beta : ℝ := inverseSpectralParameter amplitude
  let dx : ℝ := first.ofLp 0 - second.ofLp 0
  let dy : ℝ := first.ofLp 1 - second.ofLp 1
  let dk : ℝ := shearKernel first - shearKernel second
  let vertical : ℝ := dy + amplitude * dk
  let envelope : ℝ := beta * |dx| + (1 + beta) * |vertical|
  have hbeta : 0 ≤ beta := by
    dsimp [beta]
    exact inverseSpectralParameter_nonneg ha ha1
  have hdy : |dy| ≤ envelope := by
    dsimp [envelope, beta, dx, dy, dk, vertical]
    exact intrinsicShear_input_vertical_abs_le_inverseEnvelope ha ha1 first second
  have henvelope0 : 0 ≤ envelope := by
    dsimp [envelope]
    positivity
  have hdySq : dy ^ 2 ≤ envelope ^ 2 := by
    have hmul := mul_self_le_mul_self (abs_nonneg dy) hdy
    simpa [pow_two] using hmul
  have hquad := forward_spectral_quadratic_bound hbeta |dx| |vertical|
  have hchain :
      dx ^ 2 + dy ^ 2 ≤
        inverseSpectralSq amplitude * (dx ^ 2 + vertical ^ 2) := by
    calc
      dx ^ 2 + dy ^ 2 ≤ dx ^ 2 + envelope ^ 2 := by linarith
      _ = |dx| ^ 2 +
          (beta * |dx| + (1 + beta) * |vertical|) ^ 2 := by
            dsimp [envelope]
            rw [sq_abs]
      _ ≤ forwardSpectralSq beta * (|dx| ^ 2 + |vertical| ^ 2) := hquad
      _ = inverseSpectralSq amplitude * (dx ^ 2 + vertical ^ 2) := by
            dsimp [inverseSpectralSq, beta]
            rw [sq_abs, sq_abs]
  rw [dist_sq_eq_coordinate_sq_sum]
  rw [intrinsicShearMap_dist_sq_eq]
  exact hchain

theorem intrinsicShearMap_colipschitz_inverseSpectralConstant
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (ha1 : amplitude < 1)
    (first second : AmbientPlane) :
    dist first second ≤
      inverseSpectralConstant amplitude *
        dist (intrinsicShearMap amplitude first)
          (intrinsicShearMap amplitude second) := by
  have hbeta := inverseSpectralParameter_nonneg ha ha1
  have hspectral0 : 0 ≤ inverseSpectralSq amplitude := by
    dsimp [inverseSpectralSq]
    exact forward_spectral_sq_nonneg hbeta
  have hsquare :=
    intrinsicShearMap_colipschitz_sq_inverseSpectralSq ha ha1 first second
  have hconstant0 : 0 ≤ inverseSpectralConstant amplitude := by
    exact Real.sqrt_nonneg _
  have hconstantSq :
      inverseSpectralConstant amplitude ^ 2 = inverseSpectralSq amplitude := by
    dsimp [inverseSpectralConstant]
    exact Real.sq_sqrt hspectral0
  have hright0 :
      0 ≤ inverseSpectralConstant amplitude *
        dist (intrinsicShearMap amplitude first)
          (intrinsicShearMap amplitude second) :=
    mul_nonneg hconstant0 dist_nonneg
  have hsquare' :
      dist first second ^ 2 ≤
        (inverseSpectralConstant amplitude *
          dist (intrinsicShearMap amplitude first)
            (intrinsicShearMap amplitude second)) ^ 2 := by
    rw [mul_pow, hconstantSq]
    exact hsquare
  nlinarith [dist_nonneg (x := first) (y := second)]

def BackwardMapMetricBound (amplitude constant : ℝ) : Prop :=
  ∀ first second : AmbientPlane,
    dist first second ≤
      constant * dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second)

theorem inverseSpectralConstant_is_backward_metric_bound
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (ha1 : amplitude < 1) :
    BackwardMapMetricBound amplitude (inverseSpectralConstant amplitude) := by
  exact intrinsicShearMap_colipschitz_inverseSpectralConstant ha ha1

def kernelPositiveDirectionalPoint (t x y : ℝ) : AmbientPlane :=
  planeEmbedding
    ({ x := t * x, y := t * y } :
      LocalSegmentRealCompletion.RealPlanePoint)

lemma shearKernel_kernelPositiveDirectionalPoint
    {t x y : ℝ}
    (htx0 : 0 ≤ t * x) (htx1 : t * x ≤ 1)
    (hty0 : 0 ≤ t * y) (hty1 : t * y ≤ 1) :
    shearKernel (kernelPositiveDirectionalPoint t x y) =
      (1 - t * x) * (1 - t * y) := by
  simp [kernelPositiveDirectionalPoint, shearKernel, planeEmbedding,
    CompactTentHomeomorphism.tentBump, abs_of_nonneg htx0,
    abs_of_nonneg hty0, htx1, hty1]

lemma dist_kernelOrigin_kernelPositiveDirectionalPoint_sq
    (t x y : ℝ) :
    dist IntrinsicNonradialShearKernelSharp.kernelOrigin
      (kernelPositiveDirectionalPoint t x y) ^ 2 =
        (t * x) ^ 2 + (t * y) ^ 2 := by
  rw [dist_sq_eq_coordinate_sq_sum]
  simp [IntrinsicNonradialShearKernelSharp.kernelOrigin,
    kernelPositiveDirectionalPoint, planeEmbedding]

lemma intrinsicShearMap_kernelPositiveDirectionalPoint_sq
    {amplitude t x y : ℝ}
    (htx0 : 0 ≤ t * x) (htx1 : t * x ≤ 1)
    (hty0 : 0 ≤ t * y) (hty1 : t * y ≤ 1) :
    dist
      (intrinsicShearMap amplitude
        IntrinsicNonradialShearKernelSharp.kernelOrigin)
      (intrinsicShearMap amplitude
        (kernelPositiveDirectionalPoint t x y)) ^ 2 =
        (t * x) ^ 2 +
          (t * y - amplitude *
            (1 - (1 - t * x) * (1 - t * y))) ^ 2 := by
  rw [intrinsicShearMap_dist_sq_eq]
  rw [IntrinsicNonradialShearKernelSharp.shearKernel_kernelOrigin]
  rw [shearKernel_kernelPositiveDirectionalPoint htx0 htx1 hty0 hty1]
  simp [IntrinsicNonradialShearKernelSharp.kernelOrigin,
    kernelPositiveDirectionalPoint, planeEmbedding]
  ring

lemma backward_map_metric_bound_ge_one_at_zero
    {constant : ℝ} (hbound : BackwardMapMetricBound 0 constant) :
    1 ≤ constant := by
  let point := kernelPositiveDirectionalPoint 1 1 0
  have hdistSq :
      dist IntrinsicNonradialShearKernelSharp.kernelOrigin point ^ 2 = 1 := by
    dsimp [point]
    rw [dist_kernelOrigin_kernelPositiveDirectionalPoint_sq]
    norm_num
  have hdist :
      dist IntrinsicNonradialShearKernelSharp.kernelOrigin point = 1 := by
    have hnonneg :
        0 ≤ dist IntrinsicNonradialShearKernelSharp.kernelOrigin point :=
      dist_nonneg
    nlinarith
  have houtputSq :
      dist
          (intrinsicShearMap 0
            IntrinsicNonradialShearKernelSharp.kernelOrigin)
          (intrinsicShearMap 0 point) ^ 2 = 1 := by
    dsimp [point]
    rw [intrinsicShearMap_kernelPositiveDirectionalPoint_sq
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have houtput :
      dist
          (intrinsicShearMap 0
            IntrinsicNonradialShearKernelSharp.kernelOrigin)
          (intrinsicShearMap 0 point) = 1 := by
    have hnonneg :
        0 ≤ dist
          (intrinsicShearMap 0
            IntrinsicNonradialShearKernelSharp.kernelOrigin)
          (intrinsicShearMap 0 point) :=
      dist_nonneg
    nlinarith
  have h := hbound IntrinsicNonradialShearKernelSharp.kernelOrigin point
  rw [hdist, houtput] at h
  simpa using h

set_option maxHeartbeats 1000000 in
theorem backward_map_metric_bound_ge_inverseSpectralConstant
    {amplitude constant : ℝ}
    (ha : 0 ≤ amplitude) (ha1 : amplitude < 1) (hc : 0 ≤ constant)
    (hbound : BackwardMapMetricBound amplitude constant) :
    inverseSpectralConstant amplitude ≤ constant := by
  by_cases ha0 : amplitude = 0
  · subst amplitude
    have hOne := backward_map_metric_bound_ge_one_at_zero hbound
    norm_num [inverseSpectralConstant, inverseSpectralSq,
      inverseSpectralParameter, forwardSpectralSq]
    exact hOne
  · have haPos : 0 < amplitude := lt_of_le_of_ne ha (Ne.symm ha0)
    let beta : ℝ := inverseSpectralParameter amplitude
    let x : ℝ := spectralHorizontal beta
    let v : ℝ := spectralVertical beta
    let y : ℝ := spectralOutputVertical beta
    let lambda : ℝ := inverseSpectralSq amplitude
    let L : ℝ := inverseSpectralConstant amplitude
    have hbeta : 0 < beta := by
      dsimp [beta, inverseSpectralParameter]
      positivity
    have hx : 0 < x := by
      dsimp [x, spectralHorizontal]
      positivity
    have hv : 0 < v := by
      dsimp [v, spectralVertical, spectralRoot]
      positivity
    have hy : 0 < y := by
      dsimp [y, spectralOutputVertical]
      positivity
    have hN : 0 < x ^ 2 + v ^ 2 := by nlinarith [sq_pos_of_pos hv]
    have hlambda0 : 0 ≤ lambda := by
      dsimp [lambda, inverseSpectralSq]
      exact forward_spectral_sq_nonneg (le_of_lt hbeta)
    have hL0 : 0 ≤ L := by
      dsimp [L, inverseSpectralConstant]
      exact Real.sqrt_nonneg _
    have hL2 : L ^ 2 = lambda := by
      dsimp [L, inverseSpectralConstant, lambda]
      exact Real.sq_sqrt hlambda0
    have hrelation : (1 - amplitude) * y - amplitude * x = v := by
      have hne : 1 - amplitude ≠ 0 := by linarith
      dsimp [y, x, v, beta, spectralOutputVertical,
        inverseSpectralParameter]
      field_simp [hne]
      ring
    have heigen :
        x ^ 2 + y ^ 2 = lambda * (x ^ 2 + v ^ 2) := by
      dsimp [x, y, v, lambda, inverseSpectralSq, beta]
      exact spectral_eigenvector_identity hbeta
    by_contra hnot
    have hcL : constant < L := lt_of_not_ge hnot
    have hc2 : constant ^ 2 < lambda := by nlinarith
    let delta : ℝ := lambda - constant ^ 2
    let N : ℝ := x ^ 2 + v ^ 2
    let K : ℝ :=
      2 * constant ^ 2 * v * amplitude * x * y +
        constant ^ 2 * amplitude ^ 2 * x ^ 2 * y ^ 2
    let D : ℝ := delta * N + K + delta * N * x + delta * N * y
    let t : ℝ := delta * N / D
    have hdelta : 0 < delta := by dsimp [delta]; linarith
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hD : 0 < D := by
      dsimp [D]
      positivity
    have ht : 0 < t := by dsimp [t]; positivity
    have ht1 : t ≤ 1 := by
      rw [show t = (delta * N) / D by rfl]
      apply (div_le_iff₀ hD).2
      dsimp [D]
      nlinarith [mul_pos hdelta hN]
    have htx : t * x ≤ 1 := by
      rw [show t * x = (delta * N * x) / D by dsimp [t]; ring]
      apply (div_le_iff₀ hD).2
      dsimp [D]
      nlinarith [mul_pos hdelta hN, mul_pos (mul_pos hdelta hN) hx]
    have hty : t * y ≤ 1 := by
      rw [show t * y = (delta * N * y) / D by dsimp [t]; ring]
      apply (div_le_iff₀ hD).2
      dsimp [D]
      nlinarith [mul_pos hdelta hN, mul_pos (mul_pos hdelta hN) hy]
    have hKt : K * t < delta * N := by
      have hKD : K < D := by
        dsimp [D]
        nlinarith [mul_pos hdelta hN]
      rw [show K * t = (K * (delta * N)) / D by dsimp [t]; ring]
      apply (div_lt_iff₀ hD).2
      have hmul := mul_lt_mul_of_pos_left hKD (mul_pos hdelta hN)
      nlinarith
    let probe : AmbientPlane := kernelPositiveDirectionalPoint t x y
    have hinput :
        dist IntrinsicNonradialShearKernelSharp.kernelOrigin probe ^ 2 =
          t ^ 2 * lambda * N := by
      dsimp [probe]
      rw [dist_kernelOrigin_kernelPositiveDirectionalPoint_sq]
      dsimp [N]
      calc
        (t * x) ^ 2 + (t * y) ^ 2 =
            t ^ 2 * (x ^ 2 + y ^ 2) := by ring
        _ = t ^ 2 * (lambda * (x ^ 2 + v ^ 2)) := by rw [heigen]
        _ = t ^ 2 * lambda * (x ^ 2 + v ^ 2) := by ring
    have houtput :
        dist
          (intrinsicShearMap amplitude
            IntrinsicNonradialShearKernelSharp.kernelOrigin)
          (intrinsicShearMap amplitude probe) ^ 2 =
            t ^ 2 * (x ^ 2 + (v + amplitude * t * x * y) ^ 2) := by
      dsimp [probe]
      rw [intrinsicShearMap_kernelPositiveDirectionalPoint_sq
        (mul_nonneg (le_of_lt ht) (le_of_lt hx)) htx
        (mul_nonneg (le_of_lt ht) (le_of_lt hy)) hty]
      change
        (t * x) ^ 2 +
            (t * y - amplitude *
              (1 - (1 - t * x) * (1 - t * y))) ^ 2 =
          t ^ 2 * (x ^ 2 + (v + amplitude * t * x * y) ^ 2)
      rw [← hrelation]
      ring
    have htSqLe : t ^ 2 ≤ t := by nlinarith [sq_nonneg t]
    have hcoeff :
        0 ≤ constant ^ 2 * amplitude ^ 2 * x ^ 2 * y ^ 2 := by
      positivity
    have hextra :
        constant ^ 2 *
            (2 * v * amplitude * t * x * y +
              amplitude ^ 2 * t ^ 2 * x ^ 2 * y ^ 2) ≤
          K * t := by
      have hsecond := mul_le_mul_of_nonneg_left htSqLe hcoeff
      calc
        constant ^ 2 *
            (2 * v * amplitude * t * x * y +
              amplitude ^ 2 * t ^ 2 * x ^ 2 * y ^ 2) =
          2 * constant ^ 2 * v * amplitude * x * y * t +
            (constant ^ 2 * amplitude ^ 2 * x ^ 2 * y ^ 2) * t ^ 2 := by
              ring
        _ ≤ 2 * constant ^ 2 * v * amplitude * x * y * t +
            (constant ^ 2 * amplitude ^ 2 * x ^ 2 * y ^ 2) * t := by
              linarith
        _ = K * t := by dsimp [K]; ring
    have hstrictCore :
        constant ^ 2 * (x ^ 2 + (v + amplitude * t * x * y) ^ 2) <
          lambda * N := by
      calc
        constant ^ 2 * (x ^ 2 + (v + amplitude * t * x * y) ^ 2) =
            constant ^ 2 * (x ^ 2 + v ^ 2) +
              constant ^ 2 *
                (2 * v * amplitude * t * x * y +
                  amplitude ^ 2 * t ^ 2 * x ^ 2 * y ^ 2) := by ring
        _ ≤ constant ^ 2 * (x ^ 2 + v ^ 2) + K * t :=
          by linarith
        _ < constant ^ 2 * (x ^ 2 + v ^ 2) + delta * N :=
          by linarith
        _ = lambda * N := by dsimp [delta, N]; ring
    have hstrictSq :
        constant ^ 2 *
            dist
              (intrinsicShearMap amplitude
                IntrinsicNonradialShearKernelSharp.kernelOrigin)
              (intrinsicShearMap amplitude probe) ^ 2 <
          dist IntrinsicNonradialShearKernelSharp.kernelOrigin probe ^ 2 := by
      rw [hinput, houtput]
      have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
      calc
        constant ^ 2 *
            (t ^ 2 * (x ^ 2 + (v + amplitude * t * x * y) ^ 2)) =
          t ^ 2 *
            (constant ^ 2 *
              (x ^ 2 + (v + amplitude * t * x * y) ^ 2)) := by ring
        _ < t ^ 2 * (lambda * N) :=
          mul_lt_mul_of_pos_left hstrictCore ht2
        _ = t ^ 2 * lambda * N := by ring
    have hmetric :=
      hbound IntrinsicNonradialShearKernelSharp.kernelOrigin probe
    have hmetricSq :
        dist IntrinsicNonradialShearKernelSharp.kernelOrigin probe ^ 2 ≤
          constant ^ 2 *
            dist
              (intrinsicShearMap amplitude
                IntrinsicNonradialShearKernelSharp.kernelOrigin)
              (intrinsicShearMap amplitude probe) ^ 2 := by
      have hmul := mul_self_le_mul_self
        (dist_nonneg :
          0 ≤ dist IntrinsicNonradialShearKernelSharp.kernelOrigin probe)
        hmetric
      nlinarith
    linarith

theorem backward_map_metric_bound_iff
    {amplitude constant : ℝ}
    (ha : 0 ≤ amplitude) (ha1 : amplitude < 1) (hc : 0 ≤ constant) :
    BackwardMapMetricBound amplitude constant ↔
      inverseSpectralConstant amplitude ≤ constant := by
  constructor
  · exact backward_map_metric_bound_ge_inverseSpectralConstant ha ha1 hc
  · intro hconstant first second
    calc
      dist first second ≤
          inverseSpectralConstant amplitude *
            dist (intrinsicShearMap amplitude first)
              (intrinsicShearMap amplitude second) :=
        intrinsicShearMap_colipschitz_inverseSpectralConstant
          ha ha1 first second
      _ ≤ constant *
          dist (intrinsicShearMap amplitude first)
            (intrinsicShearMap amplitude second) :=
        mul_le_mul_of_nonneg_right hconstant dist_nonneg

end BoundaryOfSelf.IntrinsicNonradialShearSpectralMap
