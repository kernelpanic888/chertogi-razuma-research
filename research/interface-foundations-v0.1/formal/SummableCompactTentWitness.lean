import CompactTentHomeomorphism

namespace BoundaryOfSelf
namespace SummableCompactTentWitness

noncomputable section

open Filter
open Set
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport
open ControlledEquivComposition
open FiniteControlledChain
open TwoSidedLimitHomeomorph
open SummableTranslationWitness
open CompactTentHomeomorphism

def localAmplitude (n : Nat) : Real :=
  (1 / 2 : Real) * targetShift n

@[simp]
theorem localAmplitude_zero : localAmplitude 0 = 0 := by
  simp [localAmplitude, targetShift]

theorem localAmplitude_nonnegative (n : Nat) : 0 <= localAmplitude n := by
  have hPow : (1 / 2 : Real) ^ n <= 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  simp only [localAmplitude, targetShift]
  nlinarith

theorem localAmplitude_le_half (n : Nat) : localAmplitude n <= 1 / 2 := by
  have hPow : 0 <= (1 / 2 : Real) ^ n := pow_nonneg (by norm_num) n
  simp only [localAmplitude, targetShift]
  nlinarith

theorem localAmplitude_lt_one (n : Nat) : localAmplitude n < 1 := by
  linarith [localAmplitude_le_half n]

theorem localAmplitude_mono_step (n : Nat) :
    localAmplitude n <= localAmplitude (n + 1) := by
  have hPow : 0 <= (1 / 2 : Real) ^ n := pow_nonneg (by norm_num) n
  simp only [localAmplitude, targetShift, pow_succ]
  nlinarith

theorem localAmplitude_tendsto_half :
    Tendsto localAmplitude atTop (nhds (1 / 2 : Real)) := by
  change Tendsto (fun n => (1 / 2 : Real) * targetShift n) atTop
    (nhds (1 / 2 : Real))
  simpa using targetShift_tendsto_one.const_mul (1 / 2 : Real)

def localTentPrefix (n : Nat) : ControlledEquiv Real Real :=
  tentControlled (localAmplitude n) (localAmplitude_nonnegative n)
    (localAmplitude_lt_one n)

def limitLocalTent : Real ≃ₜ Real :=
  tentHomeomorph (1 / 2 : Real) (by norm_num) (by norm_num)

@[simp]
theorem localTentPrefix_apply (n : Nat) (point : Real) :
    localTentPrefix n point = tentMap (localAmplitude n) point := rfl

@[simp]
theorem limitLocalTent_apply (point : Real) :
    limitLocalTent point = tentMap (1 / 2 : Real) point := rfl

theorem bump_increment_abs_le
    {first second : Real} (hOrder : first <= second) :
    |tentBump second - tentBump first| <= second - first := by
  have hLip := tentBump_lipschitz.dist_le_mul second first
  rw [Real.dist_eq, Real.dist_eq] at hLip
  have hDistance : |second - first| = second - first :=
    abs_of_nonneg (sub_nonneg.mpr hOrder)
  simpa only [NNReal.coe_one, one_mul, hDistance] using hLip

theorem tentMap_increment_upper
    (firstAmplitude secondAmplitude : Real)
    (hOrderAmplitude : firstAmplitude <= secondAmplitude)
    {first second : Real} (hOrder : first <= second) :
    (1 + firstAmplitude) *
        (tentMap secondAmplitude second - tentMap secondAmplitude first) <=
      (1 + secondAmplitude) *
        (tentMap firstAmplitude second - tentMap firstAmplitude first) := by
  have hAbs := bump_increment_abs_le hOrder
  have hUpper : tentBump second - tentBump first <= second - first :=
    le_trans (le_abs_self _) hAbs
  simp only [tentMap]
  nlinarith

theorem tentMap_increment_lower
    (firstAmplitude secondAmplitude : Real)
    (hOrderAmplitude : firstAmplitude <= secondAmplitude)
    {first second : Real} (hOrder : first <= second) :
    (1 - secondAmplitude) *
        (tentMap firstAmplitude second - tentMap firstAmplitude first) <=
      (1 - firstAmplitude) *
        (tentMap secondAmplitude second - tentMap secondAmplitude first) := by
  have hAbs := bump_increment_abs_le hOrder
  have hLower : -(second - first) <= tentBump second - tentBump first :=
    le_trans (neg_le_neg hAbs) (neg_abs_le _)
  simp only [tentMap]
  nlinarith

theorem tentMap_forward_ratio_bound
    (firstAmplitude secondAmplitude : Real)
    (hFirstNonnegative : 0 <= firstAmplitude)
    (hSecondNonnegative : 0 <= secondAmplitude)
    (hFirstSmall : firstAmplitude < 1)
    (hSecondSmall : secondAmplitude < 1)
    (hAmplitudeOrder : firstAmplitude <= secondAmplitude)
    (first second : Real) :
    dist (tentMap secondAmplitude first) (tentMap secondAmplitude second) <=
      ((1 + secondAmplitude) / (1 + firstAmplitude)) *
        dist (tentMap firstAmplitude first) (tentMap firstAmplitude second) := by
  rcases le_total first second with hOrder | hOrder
  · have hIncrement := tentMap_increment_upper firstAmplitude secondAmplitude
      hAmplitudeOrder hOrder
    have hFirstMapOrder :=
      (tentMap_strictMono firstAmplitude hFirstNonnegative hFirstSmall).monotone hOrder
    have hSecondMapOrder :=
      (tentMap_strictMono secondAmplitude hSecondNonnegative hSecondSmall).monotone hOrder
    rw [Real.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hSecondMapOrder),
      abs_of_nonpos (sub_nonpos.mpr hFirstMapOrder)]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (by linarith : 0 < 1 + firstAmplitude)).2 (by
      simpa only [mul_comm, neg_sub] using hIncrement)
  · have hIncrement := tentMap_increment_upper firstAmplitude secondAmplitude
      hAmplitudeOrder hOrder
    have hFirstMapOrder :=
      (tentMap_strictMono firstAmplitude hFirstNonnegative hFirstSmall).monotone hOrder
    have hSecondMapOrder :=
      (tentMap_strictMono secondAmplitude hSecondNonnegative hSecondSmall).monotone hOrder
    rw [Real.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hSecondMapOrder),
      abs_of_nonneg (sub_nonneg.mpr hFirstMapOrder)]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (by linarith : 0 < 1 + firstAmplitude)).2 (by
      simpa only [mul_comm] using hIncrement)

theorem tentMap_inverse_ratio_bound
    (firstAmplitude secondAmplitude : Real)
    (hFirstNonnegative : 0 <= firstAmplitude)
    (hSecondNonnegative : 0 <= secondAmplitude)
    (hFirstSmall : firstAmplitude < 1)
    (hSecondSmall : secondAmplitude < 1)
    (hAmplitudeOrder : firstAmplitude <= secondAmplitude)
    (first second : Real) :
    dist (tentMap firstAmplitude first) (tentMap firstAmplitude second) <=
      ((1 - firstAmplitude) / (1 - secondAmplitude)) *
        dist (tentMap secondAmplitude first) (tentMap secondAmplitude second) := by
  rcases le_total first second with hOrder | hOrder
  · have hIncrement := tentMap_increment_lower firstAmplitude secondAmplitude
      hAmplitudeOrder hOrder
    have hFirstMapOrder :=
      (tentMap_strictMono firstAmplitude hFirstNonnegative hFirstSmall).monotone hOrder
    have hSecondMapOrder :=
      (tentMap_strictMono secondAmplitude hSecondNonnegative hSecondSmall).monotone hOrder
    rw [Real.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hFirstMapOrder),
      abs_of_nonpos (sub_nonpos.mpr hSecondMapOrder)]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (by linarith : 0 < 1 - secondAmplitude)).2 (by
      simpa only [mul_comm, neg_sub] using hIncrement)
  · have hIncrement := tentMap_increment_lower firstAmplitude secondAmplitude
      hAmplitudeOrder hOrder
    have hFirstMapOrder :=
      (tentMap_strictMono firstAmplitude hFirstNonnegative hFirstSmall).monotone hOrder
    have hSecondMapOrder :=
      (tentMap_strictMono secondAmplitude hSecondNonnegative hSecondSmall).monotone hOrder
    rw [Real.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hFirstMapOrder),
      abs_of_nonneg (sub_nonneg.mpr hSecondMapOrder)]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (by linarith : 0 < 1 - secondAmplitude)).2 (by
      simpa only [mul_comm] using hIncrement)

def localTentStep (n : Nat) : ControlledEquiv Real Real where
  toHomeomorph :=
    (localTentPrefix n).toHomeomorph.symm.trans
      (localTentPrefix (n + 1)).toHomeomorph
  forwardConstant :=
    ((1 + localAmplitude (n + 1)) / (1 + localAmplitude n)).toNNReal
  inverseConstant :=
    ((1 - localAmplitude n) / (1 - localAmplitude (n + 1))).toNNReal
  forward_lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    rw [Real.coe_toNNReal _ (div_nonneg
      (by linarith [localAmplitude_nonnegative (n + 1)])
      (by linarith [localAmplitude_nonnegative n]))]
    change dist
        (tentMap (localAmplitude (n + 1))
          ((localTentPrefix n).toHomeomorph.symm first))
        (tentMap (localAmplitude (n + 1))
          ((localTentPrefix n).toHomeomorph.symm second)) <=
      ((1 + localAmplitude (n + 1)) / (1 + localAmplitude n)) *
        dist first second
    have hBound := tentMap_forward_ratio_bound
      (localAmplitude n) (localAmplitude (n + 1))
      (localAmplitude_nonnegative n) (localAmplitude_nonnegative (n + 1))
      (localAmplitude_lt_one n) (localAmplitude_lt_one (n + 1))
      (localAmplitude_mono_step n)
      ((localTentPrefix n).toHomeomorph.symm first)
      ((localTentPrefix n).toHomeomorph.symm second)
    have hFirst : tentMap (localAmplitude n)
        ((localTentPrefix n).toHomeomorph.symm first) = first := by
      change localTentPrefix n ((localTentPrefix n).toHomeomorph.symm first) = first
      exact (localTentPrefix n).toHomeomorph.apply_symm_apply first
    have hSecond : tentMap (localAmplitude n)
        ((localTentPrefix n).toHomeomorph.symm second) = second := by
      change localTentPrefix n ((localTentPrefix n).toHomeomorph.symm second) = second
      exact (localTentPrefix n).toHomeomorph.apply_symm_apply second
    rw [hFirst, hSecond] at hBound
    exact hBound
  inverse_lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    rw [Real.coe_toNNReal _ (div_nonneg
      (by linarith [localAmplitude_lt_one n])
      (by linarith [localAmplitude_lt_one (n + 1)]))]
    change dist
        (tentMap (localAmplitude n)
          ((localTentPrefix (n + 1)).toHomeomorph.symm first))
        (tentMap (localAmplitude n)
          ((localTentPrefix (n + 1)).toHomeomorph.symm second)) <=
      ((1 - localAmplitude n) / (1 - localAmplitude (n + 1))) *
        dist first second
    have hBound := tentMap_inverse_ratio_bound
      (localAmplitude n) (localAmplitude (n + 1))
      (localAmplitude_nonnegative n) (localAmplitude_nonnegative (n + 1))
      (localAmplitude_lt_one n) (localAmplitude_lt_one (n + 1))
      (localAmplitude_mono_step n)
      ((localTentPrefix (n + 1)).toHomeomorph.symm first)
      ((localTentPrefix (n + 1)).toHomeomorph.symm second)
    have hFirst : tentMap (localAmplitude (n + 1))
        ((localTentPrefix (n + 1)).toHomeomorph.symm first) = first := by
      change localTentPrefix (n + 1)
        ((localTentPrefix (n + 1)).toHomeomorph.symm first) = first
      exact (localTentPrefix (n + 1)).toHomeomorph.apply_symm_apply first
    have hSecond : tentMap (localAmplitude (n + 1))
        ((localTentPrefix (n + 1)).toHomeomorph.symm second) = second := by
      change localTentPrefix (n + 1)
        ((localTentPrefix (n + 1)).toHomeomorph.symm second) = second
      exact (localTentPrefix (n + 1)).toHomeomorph.apply_symm_apply second
    rw [hFirst, hSecond] at hBound
    exact hBound

def localTentSequence (n : Nat) : ControlledEquiv Real Real :=
  localTentStep n

theorem prefix_localTent_apply (n : Nat) (point : Real) :
    prefixControlledEquiv localTentSequence n point = localTentPrefix n point := by
  induction n with
  | zero =>
      change point = tentMap (localAmplitude 0) point
      simp [tentMap]
  | succ n inductionHypothesis =>
      change (localTentPrefix (n + 1)).toHomeomorph
          ((localTentPrefix n).toHomeomorph.symm
            (prefixControlledEquiv localTentSequence n point)) =
        localTentPrefix (n + 1) point
      rw [inductionHypothesis]
      rw [(localTentPrefix n).toHomeomorph.symm_apply_apply]

theorem prefix_localTent_inverse_apply (n : Nat) (point : Real) :
    (prefixControlledEquiv localTentSequence n).toHomeomorph.symm point =
      (localTentPrefix n).toHomeomorph.symm point := by
  apply (localTentPrefix n).toHomeomorph.injective
  have hPrefix :=
    (prefixControlledEquiv localTentSequence n).toHomeomorph.apply_symm_apply point
  rw [prefix_localTent_apply] at hPrefix
  rw [hPrefix, (localTentPrefix n).toHomeomorph.apply_symm_apply]

theorem forward_ratio_telescope (first second : Real)
    (hFirst : 0 <= first) (hOrder : first <= second) :
    ((1 + second) / (1 + first)).toNNReal * (1 + first).toNNReal =
      (1 + second).toNNReal := by
  have hFirstPositive : 0 < 1 + first := by linarith
  have hSecondPositive : 0 < 1 + second := by linarith
  apply NNReal.eq
  simp only [NNReal.coe_mul]
  rw [Real.coe_toNNReal _ (div_nonneg (le_of_lt hSecondPositive)
      (le_of_lt hFirstPositive)),
    Real.coe_toNNReal _ (le_of_lt hFirstPositive),
    Real.coe_toNNReal _ (le_of_lt hSecondPositive)]
  field_simp [ne_of_gt hFirstPositive]

theorem inverse_ratio_telescope (first second : Real)
    (hFirstSmall : first < 1) (hSecondSmall : second < 1) :
    (1 / (1 - first)).toNNReal *
        ((1 - first) / (1 - second)).toNNReal =
      (1 / (1 - second)).toNNReal := by
  have hFirstPositive : 0 < 1 - first := by linarith
  have hSecondPositive : 0 < 1 - second := by linarith
  apply NNReal.eq
  simp only [NNReal.coe_mul]
  rw [Real.coe_toNNReal _ (le_of_lt (one_div_pos.mpr hFirstPositive)),
    Real.coe_toNNReal _ (div_nonneg (le_of_lt hFirstPositive)
      (le_of_lt hSecondPositive)),
    Real.coe_toNNReal _ (le_of_lt (one_div_pos.mpr hSecondPositive))]
  field_simp [ne_of_gt hFirstPositive, ne_of_gt hSecondPositive]

theorem prefix_localTent_forwardConstant (n : Nat) :
    (prefixControlledEquiv localTentSequence n).forwardConstant =
      (1 + localAmplitude n).toNNReal := by
  induction n with
  | zero =>
      change (1 : NNReal) = (1 + localAmplitude 0).toNNReal
      norm_num
  | succ n inductionHypothesis =>
      change ((1 + localAmplitude (n + 1)) / (1 + localAmplitude n)).toNNReal *
          (prefixControlledEquiv localTentSequence n).forwardConstant =
        (1 + localAmplitude (n + 1)).toNNReal
      rw [inductionHypothesis]
      exact forward_ratio_telescope _ _ (localAmplitude_nonnegative n)
        (localAmplitude_mono_step n)

theorem prefix_localTent_inverseConstant (n : Nat) :
    (prefixControlledEquiv localTentSequence n).inverseConstant =
      (1 / (1 - localAmplitude n)).toNNReal := by
  induction n with
  | zero =>
      change (1 : NNReal) = (1 / (1 - localAmplitude 0)).toNNReal
      norm_num
  | succ n inductionHypothesis =>
      change (prefixControlledEquiv localTentSequence n).inverseConstant *
          ((1 - localAmplitude n) / (1 - localAmplitude (n + 1))).toNNReal =
        (1 / (1 - localAmplitude (n + 1))).toNNReal
      rw [inductionHypothesis]
      exact inverse_ratio_telescope _ _ (localAmplitude_lt_one n)
        (localAmplitude_lt_one (n + 1))

theorem prefix_localTent_forward_bound (n : Nat) :
    ((prefixControlledEquiv localTentSequence n).forwardConstant : Real) <= 3 / 2 := by
  rw [prefix_localTent_forwardConstant,
    Real.coe_toNNReal _ (by linarith [localAmplitude_nonnegative n])]
  linarith [localAmplitude_le_half n]

theorem prefix_localTent_inverse_bound (n : Nat) :
    ((prefixControlledEquiv localTentSequence n).inverseConstant : Real) <= 2 := by
  rw [prefix_localTent_inverseConstant,
    Real.coe_toNNReal _ (le_of_lt (one_div_pos.mpr
      (by linarith [localAmplitude_lt_one n])))]
  apply (div_le_iff₀ (by linarith [localAmplitude_lt_one n] :
    0 < 1 - localAmplitude n)).2
  linarith [localAmplitude_le_half n]

theorem prefix_localTents_tendsto_uniformly :
    TendstoUniformlyOn
      (fun n point => prefixControlledEquiv localTentSequence n point)
      limitLocalTent atTop univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hEpsilon
  have hAmplitude := localAmplitude_tendsto_half
  rw [Metric.tendsto_atTop] at hAmplitude
  obtain ⟨N, hN⟩ := hAmplitude epsilon hEpsilon
  refine eventually_atTop.2 ⟨N, fun n hn point _ => ?_⟩
  rw [prefix_localTent_apply, localTentPrefix_apply, limitLocalTent_apply]
  rw [Real.dist_eq]
  change |(point + (1 / 2 : Real) * tentBump point) -
      (point + localAmplitude n * tentBump point)| < epsilon
  calc
    |(point + (1 / 2 : Real) * tentBump point) -
        (point + localAmplitude n * tentBump point)| =
        |(1 / 2 - localAmplitude n) * tentBump point| := by
      congr 1
      ring
    _ = |1 / 2 - localAmplitude n| * |tentBump point| := abs_mul _ _
    _ <= |1 / 2 - localAmplitude n| * 1 := by
      apply mul_le_mul_of_nonneg_left
      rw [abs_of_nonneg (tentBump_nonnegative point)]
      exact tentBump_le_one point
      exact abs_nonneg _
    _ = dist (localAmplitude n) (1 / 2) := by
      rw [Real.dist_eq, abs_sub_comm]
      ring
    _ < epsilon := hN n hn

theorem inverse_prefix_localTents_tendsto_uniformly :
    TendstoUniformlyOn
      (fun n point =>
        (prefixControlledEquiv localTentSequence n).toHomeomorph.symm point)
      limitLocalTent.symm atTop univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hEpsilon
  have hHalfEpsilon : 0 < epsilon / 2 := half_pos hEpsilon
  have hAmplitude := localAmplitude_tendsto_half
  rw [Metric.tendsto_atTop] at hAmplitude
  obtain ⟨N, hN⟩ := hAmplitude (epsilon / 2) hHalfEpsilon
  refine eventually_atTop.2 ⟨N, fun n hn point _ => ?_⟩
  rw [prefix_localTent_inverse_apply]
  let current := (localTentPrefix n).toHomeomorph.symm point
  let limit := limitLocalTent.symm point
  have hCo := tentMap_colipschitz (localAmplitude n)
    (localAmplitude_nonnegative n) (localAmplitude_lt_one n) current limit
  have hCurrent : tentMap (localAmplitude n) current = point := by
    change localTentPrefix n current = point
    exact (localTentPrefix n).toHomeomorph.apply_symm_apply point
  have hLimit : tentMap (1 / 2 : Real) limit = point := by
    change limitLocalTent limit = point
    exact limitLocalTent.apply_symm_apply point
  have hMapDifference :
      dist (tentMap (localAmplitude n) current)
          (tentMap (localAmplitude n) limit) <=
        dist (localAmplitude n) (1 / 2 : Real) := by
    rw [hCurrent, ← hLimit, Real.dist_eq, Real.dist_eq]
    change |(limit + (1 / 2 : Real) * tentBump limit) -
        (limit + localAmplitude n * tentBump limit)| <=
      |localAmplitude n - 1 / 2|
    calc
      |(limit + (1 / 2 : Real) * tentBump limit) -
          (limit + localAmplitude n * tentBump limit)| =
          |(1 / 2 - localAmplitude n) * tentBump limit| := by
        congr 1
        ring
      _ = |1 / 2 - localAmplitude n| * |tentBump limit| := abs_mul _ _
      _ <= |1 / 2 - localAmplitude n| * 1 := by
        apply mul_le_mul_of_nonneg_left
        rw [abs_of_nonneg (tentBump_nonnegative limit)]
        exact tentBump_le_one limit
        exact abs_nonneg _
      _ = |localAmplitude n - 1 / 2| := by rw [abs_sub_comm, mul_one]
  have hHalfCo : (1 / 2 : Real) * dist current limit <=
      dist (localAmplitude n) (1 / 2 : Real) := by
    calc
      (1 / 2 : Real) * dist current limit <=
          (1 - localAmplitude n) * dist current limit := by
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        linarith [localAmplitude_le_half n]
      _ <= dist (tentMap (localAmplitude n) current)
          (tentMap (localAmplitude n) limit) := hCo
      _ <= dist (localAmplitude n) (1 / 2 : Real) := hMapDifference
  have hDistance : dist current limit <=
      2 * dist (localAmplitude n) (1 / 2 : Real) := by
    nlinarith
  change dist limit current < epsilon
  calc
    dist limit current = dist current limit := dist_comm _ _
    _ <= 2 * dist (localAmplitude n) (1 / 2 : Real) := hDistance
    _ < 2 * (epsilon / 2) := mul_lt_mul_of_pos_left (hN n hn) (by norm_num)
    _ = epsilon := by ring

theorem forward_prefixes_uniformCauchy :
    UniformCauchySeqOn
      (fun n point => prefixControlledEquiv localTentSequence n point)
      atTop univ :=
  prefix_localTents_tendsto_uniformly.uniformCauchySeqOn

theorem inverse_prefixes_uniformCauchy :
    UniformCauchySeqOn
      (fun n point =>
        (prefixControlledEquiv localTentSequence n).toHomeomorph.symm point)
      atTop univ :=
  inverse_prefix_localTents_tendsto_uniformly.uniformCauchySeqOn

theorem exists_compact_tent_limit
    (model : ComputableBoundaryModel Real) :
    ∃ limitHomeomorph : Real ≃ₜ Real,
      limitHomeomorph = limitLocalTent ∧
      frontier (limitHomeomorph '' model.inside) =
        limitHomeomorph '' model.interface ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          (prefixComputableBoundaryModel localTentSequence n model).interface
          (limitHomeomorph '' model.interface))
        atTop (nhds 0) ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          ((prefixComputableBoundaryModel localTentSequence n model).approximation.carrier n)
          (limitHomeomorph '' model.interface))
        atTop (nhds 0) := by
  obtain ⟨limitHomeomorph, hForwardLimit, _hInverseLimit,
    hFrontier, hMoving, hComputed⟩ :=
    exists_limit_homeomorph_and_actual_frontier
      localTentSequence model forward_prefixes_uniformCauchy
      inverse_prefixes_uniformCauchy (3 / 2) 2
      prefix_localTent_forward_bound prefix_localTent_inverse_bound
  have hExact : limitHomeomorph = limitLocalTent := by
    ext point
    exact tendsto_nhds_unique
      (hForwardLimit.tendsto_at (mem_univ point))
      (prefix_localTents_tendsto_uniformly.tendsto_at (mem_univ point))
  exact ⟨limitHomeomorph, hExact, hFrontier, hMoving, hComputed⟩

theorem limit_tent_is_local {point : Real} (hPoint : 1 <= |point|) :
    limitLocalTent point = point := by
  rw [limitLocalTent_apply]
  simp [tentMap, tentBump_eq_zero_of_abs_ge_one hPoint]

theorem limit_tent_is_nontrivial : limitLocalTent 0 = 1 / 2 := by
  norm_num [limitLocalTent_apply, tentMap, tentBump]

end
end SummableCompactTentWitness
end BoundaryOfSelf
