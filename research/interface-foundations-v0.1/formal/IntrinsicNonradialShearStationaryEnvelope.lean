import IntrinsicNonradialShearTangentEnvelope

open scoped Topology RealInnerProductSpace
open Set Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearStationaryEnvelope

noncomputable section

open IntrinsicNonradialShearTangentEnvelope

/-! ## IF-BS-22F-F8C22: unique stationary envelope -/

def slopeRadius (t : ℝ) : ℝ :=
  Real.sqrt (1 + t ^ 2)

lemma slopeRadius_pos (t : ℝ) : 0 < slopeRadius t := by
  exact Real.sqrt_pos.2 (by positivity)

lemma slopeRadius_ne (t : ℝ) : slopeRadius t ≠ 0 :=
  ne_of_gt (slopeRadius_pos t)

lemma slopeRadius_sq (t : ℝ) : slopeRadius t ^ 2 = 1 + t ^ 2 := by
  exact Real.sq_sqrt (by positivity)

def slopeEnvelopeProfile (amplitude t : ℝ) : ℝ :=
  (1 + t) / (1 + t ^ 2) +
    (amplitude + (1 + amplitude) * t) / slopeRadius t

def slopeStationaryBalance (amplitude t : ℝ) : ℝ :=
  (t ^ 2 + 2 * t - 1) / slopeRadius t +
    amplitude * t - (1 + amplitude)

def slopeStationaryDerivative (amplitude t : ℝ) : ℝ :=
  (t ^ 3 + 3 * t + 2) / slopeRadius t ^ 3 + amplitude

theorem hasDerivAt_slopeRadius (t : ℝ) :
    HasDerivAt slopeRadius (t / slopeRadius t) t := by
  have hinner :
      HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * t) t := by
    simpa [id_eq] using ((hasDerivAt_id t).pow 2).const_add 1
  have hinner_ne : 1 + t ^ 2 ≠ 0 := by positivity
  have hsqrt := hinner.sqrt hinner_ne
  convert hsqrt using 1
  · rfl
  · simp only [slopeRadius]
    field_simp [Real.sqrt_ne_zero'.2 (by positivity : (0 : ℝ) < 1 + t ^ 2)]

theorem hasDerivAt_slopeStationaryBalance (amplitude t : ℝ) :
    HasDerivAt (slopeStationaryBalance amplitude)
      (slopeStationaryDerivative amplitude t) t := by
  let numerator : ℝ → ℝ := fun u => u ^ 2 + 2 * u - 1
  have hnum : HasDerivAt numerator (2 * t + 2) t := by
    dsimp [numerator]
    simpa [id_eq] using (((hasDerivAt_id t).pow 2).add
      ((hasDerivAt_id t).const_mul 2)).sub_const 1
  have hquot := hnum.div (hasDerivAt_slopeRadius t) (slopeRadius_ne t)
  have hlinear :
      HasDerivAt (fun u : ℝ => amplitude * u - (1 + amplitude)) amplitude t := by
    simpa using ((hasDerivAt_id t).const_mul amplitude).sub_const (1 + amplitude)
  have hraw :
      HasDerivAt
        (fun u => numerator u / slopeRadius u +
          (amplitude * u - (1 + amplitude)))
        (((2 * t + 2) * slopeRadius t -
          numerator t * (t / slopeRadius t)) / slopeRadius t ^ 2 + amplitude) t :=
    (hnum.fun_div (hasDerivAt_slopeRadius t) (slopeRadius_ne t)).add hlinear
  have hderivative :
      ((2 * t + 2) * slopeRadius t -
          numerator t * (t / slopeRadius t)) / slopeRadius t ^ 2 + amplitude =
        slopeStationaryDerivative amplitude t := by
    unfold slopeStationaryDerivative
    dsimp [numerator]
    field_simp [slopeRadius_ne]
    rw [slopeRadius_sq]
    ring
  rw [← hderivative]
  unfold slopeStationaryBalance
  convert hraw using 1
  funext u
  dsimp [numerator]
  ring

theorem slopeStationaryDerivative_pos
    {amplitude t : ℝ} (ha0 : 0 ≤ amplitude) (ht0 : 0 ≤ t) :
    0 < slopeStationaryDerivative amplitude t := by
  have hnum : 0 < t ^ 3 + 3 * t + 2 := by
    have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht0 3
    nlinarith
  have hden : 0 < slopeRadius t ^ 3 := pow_pos (slopeRadius_pos t) 3
  exact add_pos_of_pos_of_nonneg (div_pos hnum hden) ha0

theorem slopeStationaryBalance_continuous (amplitude : ℝ) :
    Continuous (slopeStationaryBalance amplitude) :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_slopeStationaryBalance amplitude t).continuousAt

theorem slopeStationaryBalance_strictMonoOn
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    StrictMonoOn (slopeStationaryBalance amplitude) (Set.Icc 0 1) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 1)
    (slopeStationaryBalance_continuous amplitude).continuousOn
    (fun t _ => (hasDerivAt_slopeStationaryBalance amplitude t).hasDerivWithinAt)
    ?_
  intro t ht
  have htOpen : t ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa only [interior_Icc] using ht
  have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨htOpen.1.le, htOpen.2.le⟩
  exact slopeStationaryDerivative_pos ha0 htI.1

lemma slopeStationaryBalance_zero (amplitude : ℝ) :
    slopeStationaryBalance amplitude 0 = -(2 + amplitude) := by
  norm_num [slopeStationaryBalance, slopeRadius]
  ring

lemma slopeStationaryBalance_one (amplitude : ℝ) :
    slopeStationaryBalance amplitude 1 = Real.sqrt 2 - 1 := by
  let radius : ℝ := Real.sqrt 2
  have hsqrt_ne : radius ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsq : radius ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have htwo : (2 : ℝ) / radius = radius := by
    calc
      (2 : ℝ) / radius = radius ^ 2 / radius := by rw [hsq]
      _ = radius := by field_simp [hsqrt_ne]
  have htwoReal : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
    simpa [radius] using htwo
  calc
    slopeStationaryBalance amplitude 1 = (2 : ℝ) / Real.sqrt 2 - 1 := by
      unfold slopeStationaryBalance slopeRadius
      ring
    _ = Real.sqrt 2 - 1 := by rw [htwoReal]

lemma slopeStationaryBalance_zero_neg
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    slopeStationaryBalance amplitude 0 < 0 := by
  rw [slopeStationaryBalance_zero]
  linarith

lemma slopeStationaryBalance_one_pos (amplitude : ℝ) :
    0 < slopeStationaryBalance amplitude 1 := by
  rw [slopeStationaryBalance_one]
  have hsqrt_gt : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  linarith

theorem existsUnique_slopeStationaryRoot
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    ∃! t : ℝ, t ∈ Set.Icc 0 1 ∧ slopeStationaryBalance amplitude t = 0 := by
  have hzero_mem :
      (0 : ℝ) ∈ Set.Icc
        (slopeStationaryBalance amplitude 0)
        (slopeStationaryBalance amplitude 1) := by
    exact ⟨(slopeStationaryBalance_zero_neg ha0).le,
      (slopeStationaryBalance_one_pos amplitude).le⟩
  obtain ⟨t, ht, hvalue⟩ :=
    (intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
      (slopeStationaryBalance_continuous amplitude).continuousOn) hzero_mem
  refine ⟨t, ⟨ht, hvalue⟩, ?_⟩
  intro u hu
  exact (slopeStationaryBalance_strictMonoOn ha0).injOn hu.1 ht
    (hu.2.trans hvalue.symm)

noncomputable def slopeStationaryRoot (amplitude : ℝ) : ℝ :=
  Classical.choose (existsUnique_slopeStationaryRoot (show 0 ≤ |amplitude| from abs_nonneg _))

noncomputable def slopeCriticalPoint (amplitude : ℝ) : ℝ :=
  slopeStationaryRoot |amplitude|

lemma slopeCriticalPoint_mem
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    slopeCriticalPoint amplitude ∈ Set.Icc 0 1 := by
  unfold slopeCriticalPoint slopeStationaryRoot
  simpa [abs_of_nonneg ha0] using
    (Classical.choose_spec
      (existsUnique_slopeStationaryRoot (abs_nonneg amplitude))).1.1

lemma slopeCriticalPoint_balance
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    slopeStationaryBalance amplitude (slopeCriticalPoint amplitude) = 0 := by
  unfold slopeCriticalPoint slopeStationaryRoot
  simpa [abs_of_nonneg ha0] using
    (Classical.choose_spec
      (existsUnique_slopeStationaryRoot (abs_nonneg amplitude))).1.2

lemma slopeCriticalPoint_pos
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    0 < slopeCriticalPoint amplitude := by
  have hmem := slopeCriticalPoint_mem ha0
  have hne : slopeCriticalPoint amplitude ≠ 0 := by
    intro h
    have hbalance := slopeCriticalPoint_balance ha0
    rw [h, slopeStationaryBalance_zero] at hbalance
    linarith
  exact lt_of_le_of_ne hmem.1 (Ne.symm hne)

lemma slopeCriticalPoint_lt_one
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    slopeCriticalPoint amplitude < 1 := by
  have hmem := slopeCriticalPoint_mem ha0
  have hne : slopeCriticalPoint amplitude ≠ 1 := by
    intro h
    have hbalance := slopeCriticalPoint_balance ha0
    rw [h, slopeStationaryBalance_one] at hbalance
    have hsqrt_gt : 1 < Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    linarith
  exact lt_of_le_of_ne hmem.2 hne

theorem hasDerivAt_slopeEnvelopeProfile (amplitude t : ℝ) :
    HasDerivAt (slopeEnvelopeProfile amplitude)
      (-slopeStationaryBalance amplitude t / slopeRadius t ^ 3) t := by
  let firstNumerator : ℝ → ℝ := fun u => 1 + u
  let firstDenominator : ℝ → ℝ := fun u => 1 + u ^ 2
  let secondNumerator : ℝ → ℝ := fun u => amplitude + (1 + amplitude) * u
  have hfirstNum : HasDerivAt firstNumerator 1 t := by
    dsimp [firstNumerator]
    simpa using (hasDerivAt_id t).const_add 1
  have hfirstDen : HasDerivAt firstDenominator (2 * t) t := by
    dsimp [firstDenominator]
    simpa [id_eq] using ((hasDerivAt_id t).pow 2).const_add 1
  have hfirstNe : firstDenominator t ≠ 0 := by
    dsimp [firstDenominator]
    positivity
  have hsecondNum : HasDerivAt secondNumerator (1 + amplitude) t := by
    dsimp [secondNumerator]
    simpa using ((hasDerivAt_id t).const_mul (1 + amplitude)).const_add amplitude
  have hraw :
      HasDerivAt
        (fun u => firstNumerator u / firstDenominator u +
          secondNumerator u / slopeRadius u)
        ((1 * firstDenominator t - firstNumerator t * (2 * t)) /
            firstDenominator t ^ 2 +
          ((1 + amplitude) * slopeRadius t -
            secondNumerator t * (t / slopeRadius t)) / slopeRadius t ^ 2) t :=
    (hfirstNum.fun_div hfirstDen hfirstNe).add
      (hsecondNum.fun_div (hasDerivAt_slopeRadius t) (slopeRadius_ne t))
  have hderivative :
      (1 * firstDenominator t - firstNumerator t * (2 * t)) /
          firstDenominator t ^ 2 +
        ((1 + amplitude) * slopeRadius t -
          secondNumerator t * (t / slopeRadius t)) / slopeRadius t ^ 2 =
        -slopeStationaryBalance amplitude t / slopeRadius t ^ 3 := by
    unfold slopeStationaryBalance
    dsimp [firstNumerator, firstDenominator, secondNumerator]
    simp only [← slopeRadius_sq t]
    field_simp [slopeRadius_ne]
    rw [slopeRadius_sq]
    ring
  rw [← hderivative]
  unfold slopeEnvelopeProfile
  change HasDerivAt
    (fun u => firstNumerator u / firstDenominator u +
      secondNumerator u / slopeRadius u) _ t
  exact hraw

theorem slopeEnvelopeProfile_continuous (amplitude : ℝ) :
    Continuous (slopeEnvelopeProfile amplitude) :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_slopeEnvelopeProfile amplitude t).continuousAt

theorem slopeEnvelopeProfile_strictMonoOn_left
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    StrictMonoOn (slopeEnvelopeProfile amplitude)
      (Set.Icc 0 (slopeCriticalPoint amplitude)) := by
  let root := slopeCriticalPoint amplitude
  have hroot_mem : root ∈ Set.Icc (0 : ℝ) 1 := slopeCriticalPoint_mem ha0
  have hbalance : slopeStationaryBalance amplitude root = 0 :=
    slopeCriticalPoint_balance ha0
  refine strictMonoOn_of_hasDerivWithinAt_pos
    (convex_Icc 0 root)
    (slopeEnvelopeProfile_continuous amplitude).continuousOn
    (fun t _ => (hasDerivAt_slopeEnvelopeProfile amplitude t).hasDerivWithinAt)
    ?_
  intro t ht
  have htOpen : t ∈ Set.Ioo (0 : ℝ) root := by
    simpa only [interior_Icc] using ht
  have htI : t ∈ Set.Icc (0 : ℝ) root := ⟨htOpen.1.le, htOpen.2.le⟩
  have htlt : t < root := htOpen.2
  have htbig : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨htI.1, htI.2.trans hroot_mem.2⟩
  have hneg : slopeStationaryBalance amplitude t < 0 := by
    simpa [hbalance] using
      (slopeStationaryBalance_strictMonoOn ha0 htbig hroot_mem htlt)
  exact div_pos (neg_pos.2 hneg) (pow_pos (slopeRadius_pos t) 3)

theorem slopeEnvelopeProfile_strictAntiOn_right
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    StrictAntiOn (slopeEnvelopeProfile amplitude)
      (Set.Icc (slopeCriticalPoint amplitude) 1) := by
  let root := slopeCriticalPoint amplitude
  have hroot_mem : root ∈ Set.Icc (0 : ℝ) 1 := slopeCriticalPoint_mem ha0
  have hbalance : slopeStationaryBalance amplitude root = 0 :=
    slopeCriticalPoint_balance ha0
  refine strictAntiOn_of_hasDerivWithinAt_neg
    (convex_Icc root 1)
    (slopeEnvelopeProfile_continuous amplitude).continuousOn
    (fun t _ => (hasDerivAt_slopeEnvelopeProfile amplitude t).hasDerivWithinAt)
    ?_
  intro t ht
  have htOpen : t ∈ Set.Ioo root (1 : ℝ) := by
    simpa only [interior_Icc] using ht
  have htI : t ∈ Set.Icc root (1 : ℝ) := ⟨htOpen.1.le, htOpen.2.le⟩
  have hrootlt : root < t := htOpen.1
  have htbig : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hroot_mem.1.trans htI.1, htI.2⟩
  have hpos : 0 < slopeStationaryBalance amplitude t := by
    simpa [hbalance] using
      (slopeStationaryBalance_strictMonoOn ha0 hroot_mem htbig hrootlt)
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hpos)
    (pow_pos (slopeRadius_pos t) 3)

theorem slopeEnvelopeProfile_le_critical
    {amplitude t : ℝ} (ha0 : 0 ≤ amplitude) (ht : t ∈ Set.Icc 0 1) :
    slopeEnvelopeProfile amplitude t ≤
      slopeEnvelopeProfile amplitude (slopeCriticalPoint amplitude) := by
  have hroot := slopeCriticalPoint_mem ha0
  by_cases hle : t ≤ slopeCriticalPoint amplitude
  · have htleft : t ∈ Set.Icc 0 (slopeCriticalPoint amplitude) := ⟨ht.1, hle⟩
    exact (slopeEnvelopeProfile_strictMonoOn_left ha0).monotoneOn
      htleft ⟨hroot.1, le_rfl⟩ hle
  · exact (slopeEnvelopeProfile_strictAntiOn_right ha0).antitoneOn
      ⟨le_rfl, hroot.2⟩ ⟨le_of_not_ge hle, ht.2⟩ (le_of_not_ge hle)

theorem slopeEnvelopeProfile_unique_max
    {amplitude t : ℝ} (ha0 : 0 ≤ amplitude) (ht : t ∈ Set.Icc 0 1)
    (heq : slopeEnvelopeProfile amplitude t =
      slopeEnvelopeProfile amplitude (slopeCriticalPoint amplitude)) :
    t = slopeCriticalPoint amplitude := by
  have hroot := slopeCriticalPoint_mem ha0
  rcases lt_trichotomy t (slopeCriticalPoint amplitude) with hlt | hequal | hgt
  · have htleft : t ∈ Set.Icc 0 (slopeCriticalPoint amplitude) := ⟨ht.1, hlt.le⟩
    have hstrict := slopeEnvelopeProfile_strictMonoOn_left ha0
      htleft ⟨hroot.1, le_rfl⟩ hlt
    linarith
  · exact hequal
  · have htright : t ∈ Set.Icc (slopeCriticalPoint amplitude) 1 := ⟨hgt.le, ht.2⟩
    have hstrict := slopeEnvelopeProfile_strictAntiOn_right ha0
      ⟨le_rfl, hroot.2⟩ htright hgt
    linarith

def slopeCoordinates (t : ℝ) : ℝ × ℝ :=
  (1 / slopeRadius t, t / slopeRadius t)

lemma slopeCoordinates_mem
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    slopeCoordinates t ∈ FirstQuadrantUnit := by
  have hrpos := slopeRadius_pos t
  have hrne := slopeRadius_ne t
  have hrsq := slopeRadius_sq t
  have hrone : 1 ≤ slopeRadius t := by
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    have hr0 := hrpos.le
    nlinarith
  have hx0 : 0 ≤ 1 / slopeRadius t := by positivity
  have hx1 : 1 / slopeRadius t ≤ 1 :=
    (div_le_one hrpos).2 hrone
  have htr : t ≤ slopeRadius t := ht.2.trans hrone
  have hy0 : 0 ≤ t / slopeRadius t := div_nonneg ht.1 hrpos.le
  have hy1 : t / slopeRadius t ≤ 1 :=
    (div_le_one hrpos).2 htr
  have hunit :
      (1 / slopeRadius t) ^ 2 + (t / slopeRadius t) ^ 2 = 1 := by
    field_simp [hrne]
    nlinarith
  exact ⟨⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩, hunit⟩

lemma scalarTangentDensity_slopeCoordinates
    (amplitude t : ℝ) :
    scalarTangentDensity amplitude (slopeCoordinates t) =
      slopeEnvelopeProfile amplitude t := by
  have hrne := slopeRadius_ne t
  have hrsq := slopeRadius_sq t
  unfold scalarTangentDensity slopeCoordinates slopeEnvelopeProfile
  simp only [← hrsq]
  field_simp [hrne]
  ring

def swapCoordinates (coordinates : ℝ × ℝ) : ℝ × ℝ :=
  (coordinates.2, coordinates.1)

lemma swapCoordinates_mem
    {coordinates : ℝ × ℝ}
    (hcoordinates : coordinates ∈ FirstQuadrantUnit) :
    swapCoordinates coordinates ∈ FirstQuadrantUnit := by
  rcases hcoordinates with ⟨⟨hX, hY⟩, hunit⟩
  change coordinates.1 ^ 2 + coordinates.2 ^ 2 = 1 at hunit
  exact ⟨⟨hY, hX⟩, by
    dsimp [swapCoordinates]
    nlinarith⟩

lemma firstQuadrantUnit_sum_ge_one
    {coordinates : ℝ × ℝ}
    (hcoordinates : coordinates ∈ FirstQuadrantUnit) :
    1 ≤ coordinates.1 + coordinates.2 := by
  rcases hcoordinates with ⟨⟨hX, hY⟩, hunit⟩
  change coordinates.1 ^ 2 + coordinates.2 ^ 2 = 1 at hunit
  have hprod : 0 ≤ coordinates.1 * coordinates.2 :=
    mul_nonneg hX.1 hY.1
  have hsum0 : 0 ≤ coordinates.1 + coordinates.2 :=
    add_nonneg hX.1 hY.1
  nlinarith [sq_nonneg (coordinates.1 + coordinates.2 - 1)]

lemma scalarTangentDensity_le_swap
    {amplitude : ℝ} {coordinates : ℝ × ℝ}
    (hcoordinates : coordinates ∈ FirstQuadrantUnit)
    (horder : coordinates.1 ≤ coordinates.2) :
    scalarTangentDensity amplitude coordinates ≤
      scalarTangentDensity amplitude (swapCoordinates coordinates) := by
  have hsum := firstQuadrantUnit_sum_ge_one hcoordinates
  unfold scalarTangentDensity swapCoordinates
  dsimp
  nlinarith

lemma dominantCoordinates_parameterized
    {coordinates : ℝ × ℝ}
    (hcoordinates : coordinates ∈ FirstQuadrantUnit)
    (horder : coordinates.2 ≤ coordinates.1) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, coordinates = slopeCoordinates t := by
  rcases hcoordinates with ⟨⟨hX, hY⟩, hunit⟩
  change coordinates.1 ^ 2 + coordinates.2 ^ 2 = 1 at hunit
  have hXpos : 0 < coordinates.1 := by
    by_contra h
    have hXzero : coordinates.1 = 0 := le_antisymm (le_of_not_gt h) hX.1
    have hYzero : coordinates.2 = 0 :=
      le_antisymm (horder.trans_eq hXzero) hY.1
    nlinarith
  have hXne : coordinates.1 ≠ 0 := ne_of_gt hXpos
  let t : ℝ := coordinates.2 / coordinates.1
  have ht0 : 0 ≤ t := div_nonneg hY.1 hX.1
  have ht1 : t ≤ 1 := (div_le_one hXpos).2 horder
  have hradius : slopeRadius t = 1 / coordinates.1 := by
    have hinvpos : 0 < 1 / coordinates.1 := by positivity
    have hinside :
        1 + t ^ 2 = (1 / coordinates.1) ^ 2 := by
      dsimp [t]
      field_simp [hXne]
      nlinarith
    rw [slopeRadius, hinside, Real.sqrt_sq_eq_abs,
      abs_of_pos hinvpos]
  refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
  apply Prod.ext
  · dsimp [slopeCoordinates]
    rw [hradius]
    field_simp [hXne]
  · dsimp [slopeCoordinates, t]
    rw [hradius]
    field_simp [hXne]

theorem scalarTangentDensity_le_criticalProfile
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude)
    {coordinates : ℝ × ℝ}
    (hcoordinates : coordinates ∈ FirstQuadrantUnit) :
    scalarTangentDensity amplitude coordinates ≤
      slopeEnvelopeProfile amplitude (slopeCriticalPoint amplitude) := by
  by_cases horder : coordinates.2 ≤ coordinates.1
  · obtain ⟨t, ht, hparam⟩ :=
      dominantCoordinates_parameterized hcoordinates horder
    rw [hparam, scalarTangentDensity_slopeCoordinates]
    exact slopeEnvelopeProfile_le_critical ha0 ht
  · have hreverse : coordinates.1 ≤ coordinates.2 := le_of_not_ge horder
    have hswap := swapCoordinates_mem hcoordinates
    have hswapOrder :
        (swapCoordinates coordinates).2 ≤ (swapCoordinates coordinates).1 :=
      hreverse
    obtain ⟨t, ht, hparam⟩ :=
      dominantCoordinates_parameterized hswap hswapOrder
    calc
      scalarTangentDensity amplitude coordinates ≤
          scalarTangentDensity amplitude (swapCoordinates coordinates) :=
        scalarTangentDensity_le_swap hcoordinates hreverse
      _ = scalarTangentDensity amplitude (slopeCoordinates t) := by rw [hparam]
      _ = slopeEnvelopeProfile amplitude t :=
        scalarTangentDensity_slopeCoordinates amplitude t
      _ ≤ slopeEnvelopeProfile amplitude (slopeCriticalPoint amplitude) :=
        slopeEnvelopeProfile_le_critical ha0 ht

theorem exactTangentEnvelope_eq_criticalProfile
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    exactTangentEnvelope amplitude =
      slopeEnvelopeProfile amplitude (slopeCriticalPoint amplitude) := by
  apply le_antisymm
  · change scalarTangentDensity amplitude (tangentEnvelopePoint amplitude) ≤ _
    exact scalarTangentDensity_le_criticalProfile ha0
      (tangentEnvelopePoint_mem amplitude)
  · rw [← scalarTangentDensity_slopeCoordinates]
    exact scalarTangentDensity_le_exact amplitude
      (slopeCoordinates_mem (slopeCriticalPoint_mem ha0))

def halfAmplitudeStationaryPolynomial (t : ℝ) : ℝ :=
  3 * t ^ 4 + 22 * t ^ 3 - 2 * t ^ 2 - 10 * t - 5

theorem halfAmplitudeCriticalPoint_polynomial :
    halfAmplitudeStationaryPolynomial (slopeCriticalPoint (1 / 2 : ℝ)) = 0 := by
  let t := slopeCriticalPoint (1 / 2 : ℝ)
  have hbalance := slopeCriticalPoint_balance (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hrad_ne := slopeRadius_ne t
  have hdiv :
      (t ^ 2 + 2 * t - 1) / slopeRadius t = (3 - t) / 2 := by
    change slopeStationaryBalance (1 / 2 : ℝ) t = 0 at hbalance
    unfold slopeStationaryBalance at hbalance
    linarith
  have hrel :
      2 * (t ^ 2 + 2 * t - 1) = (3 - t) * slopeRadius t := by
    have hmul := (div_eq_iff hrad_ne).mp hdiv
    nlinarith
  have hsq := congrArg (fun value : ℝ => value ^ 2) hrel
  dsimp [halfAmplitudeStationaryPolynomial]
  nlinarith [slopeRadius_sq t]

lemma halfAmplitude_balance_21_25_neg :
    slopeStationaryBalance (1 / 2 : ℝ) (21 / 25 : ℝ) < 0 := by
  let t : ℝ := 21 / 25
  let radius := slopeRadius t
  have hrpos : 0 < radius := slopeRadius_pos t
  have hrsq : radius ^ 2 = 1 + t ^ 2 := slopeRadius_sq t
  have hq0 : 0 ≤ t ^ 2 + 2 * t - 1 := by norm_num [t]
  have hb0 : 0 ≤ (3 - t) / 2 := by norm_num [t]
  have hsquare :
      (t ^ 2 + 2 * t - 1) ^ 2 < (((3 - t) / 2) * radius) ^ 2 := by
    rw [mul_pow, hrsq]
    norm_num [t]
  have hlt : t ^ 2 + 2 * t - 1 < ((3 - t) / 2) * radius := by
    have hright0 : 0 ≤ ((3 - t) / 2) * radius :=
      mul_nonneg hb0 hrpos.le
    nlinarith
  have hresult : slopeStationaryBalance (1 / 2 : ℝ) t < 0 := by
    unfold slopeStationaryBalance
    have hrearrange :
        (t ^ 2 + 2 * t - 1) / radius + (1 / 2 : ℝ) * t -
            (1 + (1 / 2 : ℝ)) =
          (t ^ 2 + 2 * t - 1) / radius - (3 - t) / 2 := by ring
    rw [hrearrange]
    exact sub_neg.mpr ((div_lt_iff₀ hrpos).2 hlt)
  simpa [t] using hresult

lemma halfAmplitude_balance_17_20_pos :
    0 < slopeStationaryBalance (1 / 2 : ℝ) (17 / 20 : ℝ) := by
  let t : ℝ := 17 / 20
  let radius := slopeRadius t
  have hrpos : 0 < radius := slopeRadius_pos t
  have hrsq : radius ^ 2 = 1 + t ^ 2 := slopeRadius_sq t
  have hq0 : 0 ≤ t ^ 2 + 2 * t - 1 := by norm_num [t]
  have hb0 : 0 ≤ (3 - t) / 2 := by norm_num [t]
  have hsquare :
      (((3 - t) / 2) * radius) ^ 2 < (t ^ 2 + 2 * t - 1) ^ 2 := by
    rw [mul_pow, hrsq]
    norm_num [t]
  have hgt : ((3 - t) / 2) * radius < t ^ 2 + 2 * t - 1 := by
    have hright0 : 0 ≤ ((3 - t) / 2) * radius :=
      mul_nonneg hb0 hrpos.le
    nlinarith
  have hresult : 0 < slopeStationaryBalance (1 / 2 : ℝ) t := by
    unfold slopeStationaryBalance
    have hrearrange :
        (t ^ 2 + 2 * t - 1) / radius + (1 / 2 : ℝ) * t -
            (1 + (1 / 2 : ℝ)) =
          (t ^ 2 + 2 * t - 1) / radius - (3 - t) / 2 := by ring
    rw [hrearrange]
    exact sub_pos.mpr ((lt_div_iff₀ hrpos).2 hgt)
  simpa [t] using hresult

theorem halfAmplitudeCriticalPoint_bracket :
    (21 / 25 : ℝ) < slopeCriticalPoint (1 / 2 : ℝ) ∧
      slopeCriticalPoint (1 / 2 : ℝ) < (17 / 20 : ℝ) := by
  have ha0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hroot := slopeCriticalPoint_mem ha0
  have hrootBalance := slopeCriticalPoint_balance ha0
  have hmono := slopeStationaryBalance_strictMonoOn ha0
  constructor
  · by_contra h
    have hle : slopeCriticalPoint (1 / 2 : ℝ) ≤ 21 / 25 := le_of_not_gt h
    have hpoint : (21 / 25 : ℝ) ∈ Set.Icc 0 1 := by norm_num
    have := hmono.monotoneOn hroot hpoint hle
    rw [hrootBalance] at this
    linarith [halfAmplitude_balance_21_25_neg]
  · by_contra h
    have hle : (17 / 20 : ℝ) ≤ slopeCriticalPoint (1 / 2 : ℝ) := le_of_not_gt h
    have hpoint : (17 / 20 : ℝ) ∈ Set.Icc 0 1 := by norm_num
    have := hmono.monotoneOn hpoint hroot hle
    rw [hrootBalance] at this
    linarith [halfAmplitude_balance_17_20_pos]

noncomputable def halfAmplitudeEnvelopeValue : ℝ :=
  slopeEnvelopeProfile (1 / 2 : ℝ) (slopeCriticalPoint (1 / 2 : ℝ))

theorem halfAmplitudeEnvelopeValue_certificate :
    ∃! t : ℝ,
      t ∈ Set.Icc 0 1 ∧
      halfAmplitudeStationaryPolynomial t = 0 ∧
      (21 / 25 : ℝ) < t ∧ t < (17 / 20 : ℝ) ∧
      halfAmplitudeEnvelopeValue = slopeEnvelopeProfile (1 / 2 : ℝ) t := by
  let root := slopeCriticalPoint (1 / 2 : ℝ)
  have ha0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  refine ⟨root, ⟨slopeCriticalPoint_mem ha0,
    halfAmplitudeCriticalPoint_polynomial,
    halfAmplitudeCriticalPoint_bracket.1,
    halfAmplitudeCriticalPoint_bracket.2, rfl⟩, ?_⟩
  intro t ht
  have heq :
      slopeEnvelopeProfile (1 / 2 : ℝ) t =
        slopeEnvelopeProfile (1 / 2 : ℝ) root := by
    simpa [halfAmplitudeEnvelopeValue, root] using ht.2.2.2.2.symm
  exact slopeEnvelopeProfile_unique_max ha0 ht.1 heq

theorem halfAmplitude_exactLocalTangentModulus :
    exactLocalTangentModulus (1 / 2 : ℝ) = halfAmplitudeEnvelopeValue := by
  unfold exactLocalTangentModulus halfAmplitudeEnvelopeValue
  rw [exactTangentEnvelope_eq_criticalProfile
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  ring

end

end BoundaryOfSelf.IntrinsicNonradialShearStationaryEnvelope
