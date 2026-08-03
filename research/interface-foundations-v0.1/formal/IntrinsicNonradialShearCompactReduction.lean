import IntrinsicNonradialShearDeltaNet

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearCompactReduction

open LocalSegmentRealCompletion
open StandardHausdorffMetricBridge
open CompactTentHomeomorphism
open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearExactSupport
open IntrinsicNonradialShearKernelSharp
open IntrinsicNonradialShearSpectralMap

lemma tentBump_nonneg (coordinate : ℝ) :
    0 ≤ tentBump coordinate := by
  simp [tentBump]

lemma tentBump_le_one (coordinate : ℝ) :
    tentBump coordinate ≤ 1 := by
  dsimp [tentBump]
  exact max_le (by norm_num) (by linarith [abs_nonneg coordinate])

lemma shearKernel_nonneg (point : AmbientPlane) :
    0 ≤ shearKernel point := by
  dsimp [shearKernel]
  exact mul_nonneg
    (tentBump_nonneg (point.ofLp 0))
    (tentBump_nonneg (point.ofLp 1))

lemma shearKernel_le_one (point : AmbientPlane) :
    shearKernel point ≤ 1 := by
  dsimp [shearKernel]
  have hzero0 := tentBump_nonneg (point.ofLp 0)
  have hzero1 := tentBump_nonneg (point.ofLp 1)
  have hone0 := tentBump_le_one (point.ofLp 0)
  have hone1 := tentBump_le_one (point.ofLp 1)
  nlinarith [mul_nonneg hzero0 hzero1,
    mul_le_mul hone0 hone1 hzero1 (by norm_num : 0 ≤ (1 : ℝ))]

lemma abs_shearKernel_le_one (point : AmbientPlane) :
    |shearKernel point| ≤ 1 := by
  rw [abs_of_nonneg (shearKernel_nonneg point)]
  exact shearKernel_le_one point

lemma intrinsicShearMap_displacement_sq
    (amplitude : ℝ) (point : AmbientPlane) :
    dist (intrinsicShearMap amplitude point) point ^ 2 =
      (amplitude * shearKernel point) ^ 2 := by
  rw [dist_sq_eq_coordinate_sq_sum]
  simp [intrinsicShearMap, planeEmbedding]

lemma intrinsicShearMap_displacement
    (amplitude : ℝ) (point : AmbientPlane) :
    dist (intrinsicShearMap amplitude point) point =
      |amplitude * shearKernel point| := by
  have hsquare := intrinsicShearMap_displacement_sq amplitude point
  have hdist : 0 ≤ dist (intrinsicShearMap amplitude point) point :=
    dist_nonneg
  have habs : 0 ≤ |amplitude * shearKernel point| := abs_nonneg _
  nlinarith [sq_abs (amplitude * shearKernel point)]

theorem intrinsicShearMap_displacement_le
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (point : AmbientPlane) :
    dist (intrinsicShearMap amplitude point) point ≤ amplitude := by
  rw [intrinsicShearMap_displacement]
  rw [abs_mul, abs_of_nonneg ha]
  have hkernel := abs_shearKernel_le_one point
  nlinarith

theorem intrinsicShearMap_dist_le_add_two_amplitude
    {amplitude : ℝ} (ha : 0 ≤ amplitude)
    (first second : AmbientPlane) :
    dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second) ≤
      dist first second + 2 * amplitude := by
  have hfirst := intrinsicShearMap_displacement_le ha first
  have hsecond := intrinsicShearMap_displacement_le ha second
  calc
    dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second) ≤
      dist (intrinsicShearMap amplitude first) first +
        dist first (intrinsicShearMap amplitude second) :=
      dist_triangle _ _ _
    _ ≤ dist (intrinsicShearMap amplitude first) first +
        (dist first second +
          dist second (intrinsicShearMap amplitude second)) := by
      gcongr
      exact dist_triangle _ _ _
    _ ≤ amplitude + (dist first second + amplitude) := by
      gcongr
      simpa [dist_comm] using hsecond
    _ = dist first second + 2 * amplitude := by ring

theorem intrinsicShearMap_dist_ge_sub_two_amplitude
    {amplitude : ℝ} (ha : 0 ≤ amplitude)
    (first second : AmbientPlane) :
    dist first second ≤
      dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second) + 2 * amplitude := by
  have hfirst := intrinsicShearMap_displacement_le ha first
  have hsecond := intrinsicShearMap_displacement_le ha second
  calc
    dist first second ≤
      dist first (intrinsicShearMap amplitude first) +
        dist (intrinsicShearMap amplitude first) second :=
      dist_triangle _ _ _
    _ ≤ dist first (intrinsicShearMap amplitude first) +
        (dist (intrinsicShearMap amplitude first)
            (intrinsicShearMap amplitude second) +
          dist (intrinsicShearMap amplitude second) second) := by
      gcongr
      exact dist_triangle _ _ _
    _ ≤ amplitude +
        (dist (intrinsicShearMap amplitude first)
            (intrinsicShearMap amplitude second) + amplitude) := by
      gcongr
      · simpa [dist_comm] using hfirst
    _ = dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second) + 2 * amplitude := by ring

theorem longChord_forward_bound
    {amplitude separation : ℝ}
    (ha : 0 ≤ amplitude) (hseparation : 0 < separation)
    {first second : AmbientPlane}
    (hlong : separation ≤ dist first second) :
    dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second) ≤
      (1 + 2 * amplitude / separation) * dist first second := by
  have hadd :=
    intrinsicShearMap_dist_le_add_two_amplitude ha first second
  have hfactor : 0 ≤ 2 * amplitude / separation := by positivity
  have hscaled :
      2 * amplitude ≤
        (2 * amplitude / separation) * dist first second := by
    have hmul := mul_le_mul_of_nonneg_left hlong hfactor
    have hcancel :
        (2 * amplitude / separation) * separation = 2 * amplitude := by
      field_simp
    rw [hcancel] at hmul
    exact hmul
  nlinarith

theorem longChord_backward_bound
    {amplitude separation : ℝ}
    (ha : 0 ≤ amplitude) (hseparation : 0 < separation)
    {first second : AmbientPlane}
    (hlong :
      separation ≤
        dist (intrinsicShearMap amplitude first)
          (intrinsicShearMap amplitude second)) :
    dist first second ≤
      (1 + 2 * amplitude / separation) *
        dist (intrinsicShearMap amplitude first)
          (intrinsicShearMap amplitude second) := by
  have hadd :=
    intrinsicShearMap_dist_ge_sub_two_amplitude ha first second
  have hscaled :
      2 * amplitude ≤
        (2 * amplitude / separation) *
          dist (intrinsicShearMap amplitude first)
            (intrinsicShearMap amplitude second) := by
    have hfactor : 0 ≤ 2 * amplitude / separation := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlong hfactor
    have hcancel :
        (2 * amplitude / separation) * separation = 2 * amplitude := by
      field_simp
    rw [hcancel] at hmul
    exact hmul
  nlinarith

lemma shearKernel_eq_zero_of_not_mem_exactCarrier
    {point : AmbientPlane}
    (hnot : point ∉ intrinsicShearExactCarrier) :
    shearKernel point = 0 := by
  by_contra hkernel
  have hzero :
      tentBump (point.ofLp 0) ≠ 0 := by
    intro h
    apply hkernel
    dsimp [shearKernel]
    rw [h]
    ring
  have hone :
      tentBump (point.ofLp 1) ≠ 0 := by
    intro h
    apply hkernel
    dsimp [shearKernel]
    rw [h]
    ring
  have hzeroAbs :=
    (tentBump_ne_zero_iff_abs_lt_one (point.ofLp 0)).1 hzero
  have honeAbs :=
    (tentBump_ne_zero_iff_abs_lt_one (point.ofLp 1)).1 hone
  apply hnot
  rw [mem_intrinsicShearExactCarrier_iff]
  exact ⟨le_of_lt hzeroAbs, le_of_lt honeAbs⟩

lemma intrinsicShearMap_eq_self_of_not_mem_exactCarrier
    (amplitude : ℝ) {point : AmbientPlane}
    (hnot : point ∉ intrinsicShearExactCarrier) :
    intrinsicShearMap amplitude point = point := by
  apply (intrinsicShearMap_eq_self_iff amplitude point).2
  rw [shearKernel_eq_zero_of_not_mem_exactCarrier hnot, mul_zero]

theorem outsideCarrier_pair_is_fixed
    (amplitude : ℝ) {first second : AmbientPlane}
    (hfirst : first ∉ intrinsicShearExactCarrier)
    (hsecond : second ∉ intrinsicShearExactCarrier) :
    dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second) =
      dist first second := by
  rw [intrinsicShearMap_eq_self_of_not_mem_exactCarrier amplitude hfirst]
  rw [intrinsicShearMap_eq_self_of_not_mem_exactCarrier amplitude hsecond]

def ActiveShortChordCore (separation : ℝ) :
    Set (AmbientPlane × AmbientPlane) :=
  { pair |
    dist pair.1 pair.2 ≤ separation ∧
      (pair.1 ∈ intrinsicShearExactCarrier ∨
        pair.2 ∈ intrinsicShearExactCarrier) }

theorem chord_region_trichotomy
    {separation : ℝ} (first second : AmbientPlane) :
    (first ∉ intrinsicShearExactCarrier ∧
      second ∉ intrinsicShearExactCarrier) ∨
    separation ≤ dist first second ∨
    (first, second) ∈ ActiveShortChordCore separation := by
  by_cases hactive :
      first ∈ intrinsicShearExactCarrier ∨
        second ∈ intrinsicShearExactCarrier
  · by_cases hlong : separation ≤ dist first second
    · exact Or.inr (Or.inl hlong)
    · exact Or.inr (Or.inr ⟨le_of_not_ge hlong, hactive⟩)
  · push Not at hactive
    exact Or.inl hactive

lemma carrier_point_dist_origin_le_sqrt_two
    {point : AmbientPlane} (hpoint : point ∈ intrinsicShearExactCarrier) :
    dist kernelOrigin point ≤ Real.sqrt 2 := by
  have hcoordinates :=
    (mem_intrinsicShearExactCarrier_iff point).1 hpoint
  have hxSq : point.ofLp 0 ^ 2 ≤ 1 := by
    have habs0 : 0 ≤ |point.ofLp 0| := abs_nonneg _
    have hsquare := sq_abs (point.ofLp 0)
    nlinarith
  have hySq : point.ofLp 1 ^ 2 ≤ 1 := by
    have habs1 : 0 ≤ |point.ofLp 1| := abs_nonneg _
    have hsquare := sq_abs (point.ofLp 1)
    nlinarith
  have hdistSq :
      dist kernelOrigin point ^ 2 =
        point.ofLp 0 ^ 2 + point.ofLp 1 ^ 2 := by
    rw [dist_sq_eq_coordinate_sq_sum]
    simp [kernelOrigin, planeEmbedding]
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hdist0 : 0 ≤ dist kernelOrigin point := dist_nonneg
  nlinarith

def compactEndpointBox (radius : ℝ) : Set AmbientPlane :=
  Metric.closedBall kernelOrigin radius

def compactChordBox (radius : ℝ) :
    Set (AmbientPlane × AmbientPlane) :=
  compactEndpointBox radius ×ˢ compactEndpointBox radius

theorem compactChordBox_compact (radius : ℝ) :
    IsCompact (compactChordBox radius) := by
  exact (isCompact_closedBall kernelOrigin radius).prod
    (isCompact_closedBall kernelOrigin radius)

theorem activeShortChordCore_subset_compactBox
    {separation : ℝ} (hseparation : 0 ≤ separation) :
    ActiveShortChordCore separation ⊆
      compactChordBox (Real.sqrt 2 + separation) := by
  intro pair hpair
  rcases hpair with ⟨hshort, hactive⟩
  have hfirstSecond :
      dist kernelOrigin pair.2 ≤
        dist kernelOrigin pair.1 + dist pair.1 pair.2 :=
    dist_triangle _ _ _
  have hsecondFirst :
      dist kernelOrigin pair.1 ≤
        dist kernelOrigin pair.2 + dist pair.2 pair.1 :=
    dist_triangle _ _ _
  rcases hactive with hfirst | hsecond
  · have hfirstBound := carrier_point_dist_origin_le_sqrt_two hfirst
    have hsecondBound :
        dist kernelOrigin pair.2 ≤ Real.sqrt 2 + separation := by
      nlinarith
    constructor
    · simpa [compactEndpointBox, Metric.mem_closedBall, dist_comm] using
        (show dist kernelOrigin pair.1 ≤ Real.sqrt 2 + separation by
          nlinarith)
    · simpa [compactEndpointBox, Metric.mem_closedBall, dist_comm] using
        hsecondBound
  · have hsecondBound := carrier_point_dist_origin_le_sqrt_two hsecond
    have hfirstBound :
        dist kernelOrigin pair.1 ≤ Real.sqrt 2 + separation := by
      rw [dist_comm pair.2 pair.1] at hsecondFirst
      nlinarith
    constructor
    · simpa [compactEndpointBox, Metric.mem_closedBall, dist_comm] using
        hfirstBound
    · simpa [compactEndpointBox, Metric.mem_closedBall, dist_comm] using
        (show dist kernelOrigin pair.2 ≤ Real.sqrt 2 + separation by
          nlinarith)

def ActiveOutputShortChordCore (amplitude separation : ℝ) :
    Set (AmbientPlane × AmbientPlane) :=
  {pair |
    dist (intrinsicShearMap amplitude pair.1)
        (intrinsicShearMap amplitude pair.2) ≤ separation ∧
      (pair.1 ∈ intrinsicShearExactCarrier ∨
        pair.2 ∈ intrinsicShearExactCarrier)}

theorem output_chord_region_trichotomy
    (amplitude separation : ℝ) (first second : AmbientPlane) :
    (first ∉ intrinsicShearExactCarrier ∧
        second ∉ intrinsicShearExactCarrier) ∨
      separation ≤
        dist (intrinsicShearMap amplitude first)
          (intrinsicShearMap amplitude second) ∨
      (first, second) ∈ ActiveOutputShortChordCore amplitude separation := by
  classical
  by_cases houtside :
      first ∉ intrinsicShearExactCarrier ∧
        second ∉ intrinsicShearExactCarrier
  · exact Or.inl houtside
  · right
    by_cases hlong :
        separation ≤
          dist (intrinsicShearMap amplitude first)
            (intrinsicShearMap amplitude second)
    · exact Or.inl hlong
    · right
      have hactive :
          first ∈ intrinsicShearExactCarrier ∨
            second ∈ intrinsicShearExactCarrier := by
        by_cases hfirst : first ∈ intrinsicShearExactCarrier
        · exact Or.inl hfirst
        · by_cases hsecond : second ∈ intrinsicShearExactCarrier
          · exact Or.inr hsecond
          · exact False.elim (houtside ⟨hfirst, hsecond⟩)
      exact ⟨le_of_not_ge hlong, hactive⟩

theorem activeOutputShortChordCore_subset_compactBox
    {amplitude separation : ℝ}
    (ha : 0 ≤ amplitude) (hseparation : 0 ≤ separation) :
    ActiveOutputShortChordCore amplitude separation ⊆
      compactChordBox (Real.sqrt 2 + separation + 2 * amplitude) := by
  intro pair hpair
  rcases hpair with ⟨hshort, hactive⟩
  have hinput :=
    intrinsicShearMap_dist_ge_sub_two_amplitude ha pair.1 pair.2
  have hfirstSecond :
      dist kernelOrigin pair.2 ≤
        dist kernelOrigin pair.1 + dist pair.1 pair.2 :=
    dist_triangle _ _ _
  have hsecondFirst :
      dist kernelOrigin pair.1 ≤
        dist kernelOrigin pair.2 + dist pair.2 pair.1 :=
    dist_triangle _ _ _
  rcases hactive with hfirst | hsecond
  · have hfirstBound := carrier_point_dist_origin_le_sqrt_two hfirst
    have hsecondBound :
        dist kernelOrigin pair.2 ≤
          Real.sqrt 2 + separation + 2 * amplitude := by
      nlinarith
    constructor
    · simpa [compactEndpointBox, Metric.mem_closedBall, dist_comm] using
        (show dist kernelOrigin pair.1 ≤
            Real.sqrt 2 + separation + 2 * amplitude by
          nlinarith)
    · simpa [compactEndpointBox, Metric.mem_closedBall, dist_comm] using
        hsecondBound
  · have hsecondBound := carrier_point_dist_origin_le_sqrt_two hsecond
    have hfirstBound :
        dist kernelOrigin pair.1 ≤
          Real.sqrt 2 + separation + 2 * amplitude := by
      rw [dist_comm pair.2 pair.1] at hsecondFirst
      nlinarith
    constructor
    · simpa [compactEndpointBox, Metric.mem_closedBall, dist_comm] using
        hfirstBound
    · simpa [compactEndpointBox, Metric.mem_closedBall, dist_comm] using
        (show dist kernelOrigin pair.2 ≤
            Real.sqrt 2 + separation + 2 * amplitude by
          nlinarith)

theorem forward_global_bound_of_compactCore
    {amplitude separation coreUpper : ℝ}
    (ha : 0 ≤ amplitude) (hseparation : 0 < separation)
    (_hcoreUpper : 0 ≤ coreUpper)
    (hcore :
      ∀ pair ∈ ActiveShortChordCore separation,
        dist (intrinsicShearMap amplitude pair.1)
            (intrinsicShearMap amplitude pair.2) ≤
          coreUpper * dist pair.1 pair.2) :
    ForwardMapMetricBound amplitude
      (max 1 (max (1 + 2 * amplitude / separation) coreUpper)) := by
  intro first second
  rcases chord_region_trichotomy
      (separation := separation) first second with
    houtside | hlong | hcorePair
  · rw [outsideCarrier_pair_is_fixed amplitude houtside.1 houtside.2]
    simpa using
      (mul_le_mul_of_nonneg_right
        (le_max_left 1 (max (1 + 2 * amplitude / separation) coreUpper))
        (dist_nonneg : 0 ≤ dist first second))

  · have hfar := longChord_forward_bound ha hseparation hlong
    exact le_trans hfar
      (mul_le_mul_of_nonneg_right
        (le_trans
          (le_max_left (1 + 2 * amplitude / separation) coreUpper)
          (le_max_right 1
            (max (1 + 2 * amplitude / separation) coreUpper)))
        (dist_nonneg : 0 ≤ dist first second))
  · have hlocal := hcore (first, second) hcorePair
    exact le_trans hlocal
      (mul_le_mul_of_nonneg_right
        (le_trans
          (le_max_right (1 + 2 * amplitude / separation) coreUpper)
          (le_max_right 1
            (max (1 + 2 * amplitude / separation) coreUpper)))
        (dist_nonneg : 0 ≤ dist first second))

theorem backward_global_bound_of_compactCore
    {amplitude separation coreUpper : ℝ}
    (ha : 0 ≤ amplitude) (hseparation : 0 < separation)
    (_hcoreUpper : 0 ≤ coreUpper)
    (hcore :
      ∀ pair ∈ ActiveOutputShortChordCore amplitude separation,
        dist pair.1 pair.2 ≤
          coreUpper *
            dist (intrinsicShearMap amplitude pair.1)
              (intrinsicShearMap amplitude pair.2)) :
    BackwardMapMetricBound amplitude
      (max 1 (max (1 + 2 * amplitude / separation) coreUpper)) := by
  intro first second
  rcases output_chord_region_trichotomy
      amplitude separation first second with
    houtside | hlong | hcorePair
  · rw [outsideCarrier_pair_is_fixed amplitude houtside.1 houtside.2]
    simpa using
      (mul_le_mul_of_nonneg_right
        (le_max_left 1 (max (1 + 2 * amplitude / separation) coreUpper))
        (dist_nonneg : 0 ≤ dist first second))
  · have hfar := longChord_backward_bound ha hseparation hlong
    exact le_trans hfar
      (mul_le_mul_of_nonneg_right
        (le_trans
          (le_max_left (1 + 2 * amplitude / separation) coreUpper)
          (le_max_right 1
            (max (1 + 2 * amplitude / separation) coreUpper)))
        (dist_nonneg :
          0 ≤ dist (intrinsicShearMap amplitude first)
            (intrinsicShearMap amplitude second)))
  · have hlocal := hcore (first, second) hcorePair
    exact le_trans hlocal
      (mul_le_mul_of_nonneg_right
        (le_trans
          (le_max_right (1 + 2 * amplitude / separation) coreUpper)
          (le_max_right 1
            (max (1 + 2 * amplitude / separation) coreUpper)))
        (dist_nonneg :
          0 ≤ dist (intrinsicShearMap amplitude first)
            (intrinsicShearMap amplitude second)))
end BoundaryOfSelf.IntrinsicNonradialShearCompactReduction
