import SummableTranslationWitness

namespace BoundaryOfSelf
namespace CompactTentHomeomorphism

noncomputable section

open Set
open BiLipschitzBoundaryTransport


def tentBump (point : Real) : Real := max 0 (1 - |point|)

def tentMap (amplitude point : Real) : Real := point + amplitude * tentBump point

@[simp]
theorem tentBump_zero : tentBump 0 = 1 := by
  norm_num [tentBump]

theorem tentBump_nonnegative (point : Real) : 0 ≤ tentBump point := by
  exact le_max_left _ _

theorem tentBump_le_one (point : Real) : tentBump point ≤ 1 := by
  apply max_le
  · norm_num
  · linarith [abs_nonneg point]

theorem tentBump_eq_zero_of_abs_ge_one {point : Real} (hPoint : 1 ≤ |point|) :
    tentBump point = 0 := by
  exact max_eq_left (by linarith)

theorem tentBump_lipschitz : LipschitzWith 1 tentBump := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  simp only [NNReal.coe_one, one_mul]
  rw [Real.dist_eq, Real.dist_eq]
  calc
    |tentBump first - tentBump second| =
        |max (1 - |first|) 0 - max (1 - |second|) 0| := by
      simp only [tentBump, max_comm]
    _ ≤ |(1 - |first|) - (1 - |second|)| :=
      abs_max_sub_max_le_abs _ _ 0
    _ = |(|first| - |second|)| := by
      rw [abs_sub_comm]
      congr 1
      ring
    _ ≤ |first - second| := abs_abs_sub_abs_le first second

theorem tentMap_identity_of_le_neg_one
    (amplitude point : Real) (hPoint : point ≤ -1) :
    tentMap amplitude point = point := by
  have hAbs : 1 ≤ |point| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  simp [tentMap, tentBump_eq_zero_of_abs_ge_one hAbs]

theorem tentMap_identity_of_one_le
    (amplitude point : Real) (hPoint : 1 ≤ point) :
    tentMap amplitude point = point := by
  have hAbs : 1 ≤ |point| := le_trans hPoint (le_abs_self point)
  simp [tentMap, tentBump_eq_zero_of_abs_ge_one hAbs]

theorem tentMap_lipschitz
    (amplitude : Real) (hAmplitude : 0 ≤ amplitude) :
    LipschitzWith (1 + amplitude).toNNReal (tentMap amplitude) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [Real.coe_toNNReal (1 + amplitude) (by linarith)]
  rw [Real.dist_eq, Real.dist_eq]
  change |(first + amplitude * tentBump first) -
      (second + amplitude * tentBump second)| ≤
    (1 + amplitude) * |first - second|
  calc
    |(first + amplitude * tentBump first) -
        (second + amplitude * tentBump second)| =
        |(first - second) + amplitude * (tentBump first - tentBump second)| := by
      congr 1
      ring
    _ ≤ |first - second| + |amplitude * (tentBump first - tentBump second)| :=
      abs_add_le _ _
    _ = |first - second| + amplitude * |tentBump first - tentBump second| := by
      rw [abs_mul, abs_of_nonneg hAmplitude]
    _ ≤ |first - second| + amplitude * |first - second| := by
      have hLip := tentBump_lipschitz.dist_le_mul first second
      have hWeighted :
          amplitude * |tentBump first - tentBump second| ≤
            amplitude * |first - second| :=
        mul_le_mul_of_nonneg_left (by simpa [Real.dist_eq] using hLip) hAmplitude
      linarith
    _ = (1 + amplitude) * |first - second| := by ring

theorem tentMap_gap_lower
    (amplitude : Real) (hAmplitude : 0 ≤ amplitude)
    {first second : Real} (hOrder : first ≤ second) :
    (1 - amplitude) * (second - first) ≤
      tentMap amplitude second - tentMap amplitude first := by
  have hLip := tentBump_lipschitz.dist_le_mul first second
  have hAbsDistance : |first - second| = second - first := by
    rw [abs_of_nonpos (sub_nonpos.mpr hOrder)]
    ring
  have hBumpAbs : |tentBump second - tentBump first| ≤ second - first := by
    rw [abs_sub_comm]
    simpa [Real.dist_eq, hAbsDistance] using hLip
  have hBumpLower : -(second - first) ≤ tentBump second - tentBump first := by
    have hNegAbs := neg_abs_le (tentBump second - tentBump first)
    linarith
  change (1 - amplitude) * (second - first) ≤
    (second + amplitude * tentBump second) -
      (first + amplitude * tentBump first)
  nlinarith

theorem tentMap_strictMono
    (amplitude : Real) (hAmplitude : 0 ≤ amplitude) (hSmall : amplitude < 1) :
    StrictMono (tentMap amplitude) := by
  intro first second hOrder
  have hGap := tentMap_gap_lower amplitude hAmplitude (le_of_lt hOrder)
  have hPositive : 0 < (1 - amplitude) * (second - first) :=
    mul_pos (sub_pos.mpr hSmall) (sub_pos.mpr hOrder)
  linarith

theorem tentMap_surjective
    (amplitude : Real) (hAmplitude : 0 ≤ amplitude) :
    Function.Surjective (tentMap amplitude) := by
  intro target
  let left : Real := min target (-1)
  let right : Real := max target 1
  have hLeft : left ≤ -1 := min_le_right _ _
  have hRight : 1 ≤ right := le_max_right _ _
  have hMapLeft : tentMap amplitude left = left :=
    tentMap_identity_of_le_neg_one amplitude left hLeft
  have hMapRight : tentMap amplitude right = right :=
    tentMap_identity_of_one_le amplitude right hRight
  have hTarget : target ∈ Set.Icc (tentMap amplitude left) (tentMap amplitude right) := by
    rw [hMapLeft, hMapRight]
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  exact (intermediate_value_univ left right (tentMap_lipschitz amplitude hAmplitude).continuous)
    hTarget

def tentOrderIso
    (amplitude : Real) (hAmplitude : 0 ≤ amplitude) (hSmall : amplitude < 1) :
    Real ≃o Real :=
  StrictMono.orderIsoOfSurjective (tentMap amplitude)
    (tentMap_strictMono amplitude hAmplitude hSmall)
    (tentMap_surjective amplitude hAmplitude)

def tentHomeomorph
    (amplitude : Real) (hAmplitude : 0 ≤ amplitude) (hSmall : amplitude < 1) :
    Real ≃ₜ Real :=
  (tentOrderIso amplitude hAmplitude hSmall).toHomeomorph

@[simp]
theorem tentHomeomorph_apply
    (amplitude : Real) (hAmplitude : 0 ≤ amplitude) (hSmall : amplitude < 1)
    (point : Real) :
    tentHomeomorph amplitude hAmplitude hSmall point = tentMap amplitude point := rfl

theorem tentMap_colipschitz
    (amplitude : Real) (hAmplitude : 0 ≤ amplitude) (hSmall : amplitude < 1)
    (first second : Real) :
    (1 - amplitude) * dist first second ≤
      dist (tentMap amplitude first) (tentMap amplitude second) := by
  rcases le_total first second with hOrder | hOrder
  · have hGap := tentMap_gap_lower amplitude hAmplitude hOrder
    have hMapOrder := (tentMap_strictMono amplitude hAmplitude hSmall).monotone hOrder
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hOrder),
      abs_of_nonpos (sub_nonpos.mpr hMapOrder)]
    linarith
  · have hGap := tentMap_gap_lower amplitude hAmplitude hOrder
    have hMapOrder := (tentMap_strictMono amplitude hAmplitude hSmall).monotone hOrder
    rw [dist_comm first second, dist_comm (tentMap amplitude first) (tentMap amplitude second),
      Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hOrder),
      abs_of_nonpos (sub_nonpos.mpr hMapOrder)]
    linarith

def tentControlled
    (amplitude : Real) (hAmplitude : 0 ≤ amplitude) (hSmall : amplitude < 1) :
    ControlledEquiv Real Real where
  toHomeomorph := tentHomeomorph amplitude hAmplitude hSmall
  forwardConstant := (1 + amplitude).toNNReal
  inverseConstant := (1 / (1 - amplitude)).toNNReal
  forward_lipschitz := tentMap_lipschitz amplitude hAmplitude
  inverse_lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    rw [Real.coe_toNNReal (1 / (1 - amplitude))
      (le_of_lt (one_div_pos.mpr (sub_pos.mpr hSmall)))]
    have hCo := tentMap_colipschitz amplitude hAmplitude hSmall
      ((tentHomeomorph amplitude hAmplitude hSmall).symm first)
      ((tentHomeomorph amplitude hAmplitude hSmall).symm second)
    have hFirst : tentMap amplitude
        ((tentHomeomorph amplitude hAmplitude hSmall).symm first) = first := by
      rw [← tentHomeomorph_apply]
      exact (tentHomeomorph amplitude hAmplitude hSmall).apply_symm_apply first
    have hSecond : tentMap amplitude
        ((tentHomeomorph amplitude hAmplitude hSmall).symm second) = second := by
      rw [← tentHomeomorph_apply]
      exact (tentHomeomorph amplitude hAmplitude hSmall).apply_symm_apply second
    rw [hFirst, hSecond] at hCo
    change dist ((tentHomeomorph amplitude hAmplitude hSmall).symm first)
      ((tentHomeomorph amplitude hAmplitude hSmall).symm second) ≤
        (1 / (1 - amplitude)) * dist first second
    rw [one_div, inv_mul_eq_div]
    exact (le_div_iff₀ (sub_pos.mpr hSmall)).2 (by
      simpa [mul_comm] using hCo)

end
end CompactTentHomeomorphism
end BoundaryOfSelf
