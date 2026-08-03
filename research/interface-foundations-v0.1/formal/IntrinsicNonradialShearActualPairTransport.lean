import IntrinsicNonradialShearCenteredEnvelope

set_option maxHeartbeats 800000

namespace BoundaryOfSelf.IntrinsicNonradialShearActualPairTransport

open Set Real
open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearRealizableCertificate
open IntrinsicNonradialShearChordBridge
open IntrinsicNonradialShearCenteredEnvelope
open IntrinsicNonradialShearTangentEnvelope

/-- One-dimensional parallelogram identity.  It is the exact reason why the
mean width of two endpoints becomes a maximum of midpoint and half-chord
widths rather than their sum. -/
lemma abs_add_abs_sub_eq_two_max (m h : ℝ) :
    |m + h| + |m - h| = 2 * max |m| |h| := by
  by_cases hp : 0 ≤ m + h
  · by_cases hm : 0 ≤ m - h
    · have hhm : |h| ≤ m := abs_le.2 ⟨by linarith, by linarith⟩
      have hm0 : 0 ≤ m := (abs_nonneg h).trans hhm
      rw [abs_of_nonneg hp, abs_of_nonneg hm,
        max_eq_left (by simpa [abs_of_nonneg hm0] using hhm),
        abs_of_nonneg hm0]
      ring
    · have hm' : m - h < 0 := lt_of_not_ge hm
      have hmm : |m| ≤ h := abs_le.2 ⟨by linarith, by linarith⟩
      have hh0 : 0 ≤ h := (abs_nonneg m).trans hmm
      rw [abs_of_nonneg hp, abs_of_neg hm',
        max_eq_right (by simpa [abs_of_nonneg hh0] using hmm),
        abs_of_nonneg hh0]
      ring
  · have hp' : m + h < 0 := lt_of_not_ge hp
    by_cases hm : 0 ≤ m - h
    · have hmm : |m| ≤ -h := abs_le.2 ⟨by linarith, by linarith⟩
      have hh0 : 0 ≤ -h := (abs_nonneg m).trans hmm
      rw [abs_of_neg hp', abs_of_nonneg hm,
        max_eq_right (by simpa [abs_of_nonpos (by linarith : h ≤ 0)] using hmm),
        abs_of_nonpos (by linarith : h ≤ 0)]
      ring
    · have hm' : m - h < 0 := lt_of_not_ge hm
      have hhm : |h| ≤ -m := abs_le.2 ⟨by linarith, by linarith⟩
      have hm0 : 0 ≤ -m := (abs_nonneg h).trans hhm
      rw [abs_of_neg hp', abs_of_neg hm',
        max_eq_left (by simpa [abs_of_nonpos (by linarith : m ≤ 0)] using hhm),
        abs_of_nonpos (by linarith : m ≤ 0)]
      ring

/-- Canonical centered record of two points of the unit circle.  The antipodal
case is included; only the zero half-chord requires the explicit equal-direction
branch. -/
theorem exists_centered_record_of_unit_pair
    {x₁ y₁ x₂ y₂ : ℝ}
    (hfirst : x₁ ^ 2 + y₁ ^ 2 = 1)
    (hsecond : x₂ ^ 2 + y₂ ^ 2 = 1) :
    ∃ X Y r k : ℝ,
      0 ≤ X ∧ 0 ≤ Y ∧ 0 ≤ r ∧ 0 ≤ k ∧
      X ^ 2 + Y ^ 2 = 1 ∧ r ^ 2 + k ^ 2 = 1 ∧
      r ^ 2 = ((x₁ + x₂) / 2) ^ 2 + ((y₁ + y₂) / 2) ^ 2 ∧
      k ^ 2 = ((x₁ - x₂) / 2) ^ 2 + ((y₁ - y₂) / 2) ^ 2 ∧
      |(x₁ + x₂) / 2| = r * X ∧
      |(y₁ + y₂) / 2| = r * Y ∧
      |(x₁ - x₂) / 2| = k * Y ∧
      |(y₁ - y₂) / 2| = k * X := by
  let mx : ℝ := (x₁ + x₂) / 2
  let my : ℝ := (y₁ + y₂) / 2
  let hx : ℝ := (x₁ - x₂) / 2
  let hy : ℝ := (y₁ - y₂) / 2
  let r : ℝ := Real.sqrt (mx ^ 2 + my ^ 2)
  let k : ℝ := Real.sqrt (hx ^ 2 + hy ^ 2)
  have hmidhalf : mx ^ 2 + my ^ 2 + (hx ^ 2 + hy ^ 2) = 1 := by
    dsimp [mx, my, hx, hy]
    nlinarith
  have horth : mx * hx + my * hy = 0 := by
    dsimp [mx, my, hx, hy]
    nlinarith
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hrSq : r ^ 2 = mx ^ 2 + my ^ 2 := by
    dsimp [r]
    rw [Real.sq_sqrt (by positivity)]
  have hkSq : k ^ 2 = hx ^ 2 + hy ^ 2 := by
    dsimp [k]
    rw [Real.sq_sqrt (by positivity)]
  have hrk : r ^ 2 + k ^ 2 = 1 := by nlinarith
  by_cases hk : k = 0
  · have hhx : hx = 0 := by nlinarith [sq_nonneg hx, sq_nonneg hy]
    have hhy : hy = 0 := by nlinarith [sq_nonneg hx, sq_nonneg hy]
    have hr : r = 1 := by nlinarith
    refine ⟨|mx|, |my|, r, k, abs_nonneg _, abs_nonneg _, hr0, hk0,
      ?_, hrk, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sq_abs, sq_abs]
      nlinarith
    · simpa [mx, my] using hrSq
    · simpa [hx, hy] using hkSq
    · simp [mx, hr]
    · simp [my, hr]
    · simp [hx, hhx, hk]
    · simp [hy, hhy, hk]
  · have hkpos : 0 < k := lt_of_le_of_ne hk0 (Ne.symm hk)
    let X : ℝ := |hy| / k
    let Y : ℝ := |hx| / k
    have hX0 : 0 ≤ X := div_nonneg (abs_nonneg _) hk0
    have hY0 : 0 ≤ Y := div_nonneg (abs_nonneg _) hk0
    have hXY : X ^ 2 + Y ^ 2 = 1 := by
      dsimp [X, Y]
      field_simp [hk]
      nlinarith [sq_abs hx, sq_abs hy]
    have hprod : mx * hx = -(my * hy) := by linarith
    have hprodSq : (mx * hx) ^ 2 = (my * hy) ^ 2 := by
      rw [hprod]
      ring
    have hmxSq : mx ^ 2 * k ^ 2 = r ^ 2 * hy ^ 2 := by
      rw [hkSq, hrSq]
      calc
        mx ^ 2 * (hx ^ 2 + hy ^ 2) =
            (mx * hx) ^ 2 + (mx * hy) ^ 2 := by ring
        _ = (my * hy) ^ 2 + (mx * hy) ^ 2 := by rw [hprodSq]
        _ = (mx ^ 2 + my ^ 2) * hy ^ 2 := by ring
    have hmySq : my ^ 2 * k ^ 2 = r ^ 2 * hx ^ 2 := by
      rw [hkSq, hrSq]
      calc
        my ^ 2 * (hx ^ 2 + hy ^ 2) =
            (my * hx) ^ 2 + (my * hy) ^ 2 := by ring
        _ = (my * hx) ^ 2 + (mx * hx) ^ 2 := by rw [hprodSq]
        _ = (mx ^ 2 + my ^ 2) * hx ^ 2 := by ring
    have hmxk : |mx| * k = r * |hy| := by
      have hsquares : (|mx| * k) ^ 2 = (r * |hy|) ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs, sq_abs]
        exact hmxSq
      rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hsquares with heq | heq
      · exact heq
      ·
        have hleft0 : 0 ≤ |mx| * k := mul_nonneg (abs_nonneg mx) hk0
        have hright0 : 0 ≤ r * |hy| := mul_nonneg hr0 (abs_nonneg hy)
        nlinarith
    have hmyk : |my| * k = r * |hx| := by
      have hsquares : (|my| * k) ^ 2 = (r * |hx|) ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs, sq_abs]
        exact hmySq
      rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hsquares with heq | heq
      · exact heq
      ·
        have hleft0 : 0 ≤ |my| * k := mul_nonneg (abs_nonneg my) hk0
        have hright0 : 0 ≤ r * |hx| := mul_nonneg hr0 (abs_nonneg hx)
        nlinarith
    refine ⟨X, Y, r, k, hX0, hY0, hr0, hk0, hXY, hrk,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [mx, my] using hrSq
    · simpa [hx, hy] using hkSq
    · change |mx| = r * (|hy| / k)
      field_simp [hk]
      exact hmxk
    · change |my| = r * (|hx| / k)
      field_simp [hk]
      exact hmyk
    · change |hx| = k * (|hx| / k)
      field_simp [hk]
    · change |hy| = k * (|hy| / k)
      field_simp [hk]

/-- The averaged diamond width of an actual pair is exactly controlled by the
two max-branches of its centered record. -/
lemma centered_slope_width_bound
    {x₁ y₁ s₁ x₂ y₂ s₂ X Y r k : ℝ}
    (hs₁ : |s₁| ≤ |x₁| + |y₁|)
    (hs₂ : |s₂| ≤ |x₂| + |y₂|)
    (hmx : |(x₁ + x₂) / 2| = r * X)
    (hmy : |(y₁ + y₂) / 2| = r * Y)
    (hhx : |(x₁ - x₂) / 2| = k * Y)
    (hhy : |(y₁ - y₂) / 2| = k * X) :
    |(s₁ + s₂) / 2| ≤
      max (r * X) (k * Y) + max (r * Y) (k * X) := by
  have hsavg : |(s₁ + s₂) / 2| ≤ (|s₁| + |s₂|) / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  have hscoords : (|s₁| + |s₂|) / 2 ≤
      (|x₁| + |x₂|) / 2 + (|y₁| + |y₂|) / 2 := by
    linarith
  have hxavg : (|x₁| + |x₂|) / 2 =
      max |(x₁ + x₂) / 2| |(x₁ - x₂) / 2| := by
    calc
      (|x₁| + |x₂|) / 2 =
          (|(x₁ + x₂) / 2 + (x₁ - x₂) / 2| +
            |(x₁ + x₂) / 2 - (x₁ - x₂) / 2|) / 2 := by
              congr 2 <;> ring
      _ = max |(x₁ + x₂) / 2| |(x₁ - x₂) / 2| := by
        rw [abs_add_abs_sub_eq_two_max]
        ring
  have hyavg : (|y₁| + |y₂|) / 2 =
      max |(y₁ + y₂) / 2| |(y₁ - y₂) / 2| := by
    calc
      (|y₁| + |y₂|) / 2 =
          (|(y₁ + y₂) / 2 + (y₁ - y₂) / 2| +
            |(y₁ + y₂) / 2 - (y₁ - y₂) / 2|) / 2 := by
              congr 2 <;> ring
      _ = max |(y₁ + y₂) / 2| |(y₁ - y₂) / 2| := by
        rw [abs_add_abs_sub_eq_two_max]
        ring
  calc
    |(s₁ + s₂) / 2| ≤ (|s₁| + |s₂|) / 2 := hsavg
    _ ≤ (|x₁| + |x₂|) / 2 + (|y₁| + |y₂|) / 2 := hscoords
    _ = max (r * X) (k * Y) + max (r * Y) (k * X) := by
      rw [hxavg, hyavg, hmx, hmy, hhx, hhy]

/-- F8C25 actual-pair transport.  The exact local tangent modulus is already a
global pairwise modulus on the full realizable diamond; no positive finite-chord
correction is needed. -/
theorem forwardBlowUpSq_actual_pair_exact_bound
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude)
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand) :
    |forwardBlowUpSq amplitude first -
        forwardBlowUpSq amplitude second| ≤
      exactLocalTangentModulus amplitude * dist first second := by
  let x₁ : ℝ := first.1.ofLp 0
  let y₁ : ℝ := first.1.ofLp 1
  let s₁ : ℝ := first.2
  let x₂ : ℝ := second.1.ofLp 0
  let y₂ : ℝ := second.1.ofLp 1
  let s₂ : ℝ := second.2
  let mx : ℝ := (x₁ + x₂) / 2
  let my : ℝ := (y₁ + y₂) / 2
  let hx : ℝ := (x₁ - x₂) / 2
  let hy : ℝ := (y₁ - y₂) / 2
  let σ : ℝ := (s₁ + s₂) / 2
  let δ : ℝ := (s₁ - s₂) / 2
  let D : ℝ := dist first second
  have hD0 : 0 ≤ D := dist_nonneg
  have hdata₁ := diamond_unit_and_slope hfirst
  have hdata₂ := diamond_unit_and_slope hsecond
  rcases exists_centered_record_of_unit_pair hdata₁.1 hdata₂.1 with
    ⟨X, Y, r, k, hX0, hY0, hr0, hk0, hXY, hrk,
      hrSq, hkSq, hmx, hmy, hhx, hhy⟩
  have hσ := centered_slope_width_bound hdata₁.2 hdata₂.2
      hmx hmy hhx hhy
  let W : ℝ := max (r * X) (k * Y) + max (r * Y) (k * X)
  have hσW : |σ| ≤ W := by simpa [σ, W] using hσ
  have hW0 : 0 ≤ W := by
    dsimp [W]
    exact add_nonneg
      ((mul_nonneg hr0 hX0).trans (le_max_left _ _))
      ((mul_nonneg hr0 hY0).trans (le_max_left _ _))
  have hdirSq : dist first.1 second.1 ^ 2 = 4 * k ^ 2 := by
    have hsource :=
      IntrinsicNonradialShearExactSupport.dist_sq_eq_coordinate_sq_sum
        first.1 second.1
    calc
      dist first.1 second.1 ^ 2 =
          (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 := by
            simpa [x₁, y₁, x₂, y₂] using hsource
      _ = 4 * (((x₁ - x₂) / 2) ^ 2 + ((y₁ - y₂) / 2) ^ 2) := by ring
      _ = 4 * k ^ 2 := by rw [← hkSq]
  have hdir : dist first.1 second.1 = 2 * k := by
    have hsquare : dist first.1 second.1 ^ 2 = (2 * k) ^ 2 := by
      calc
        dist first.1 second.1 ^ 2 = 4 * k ^ 2 := hdirSq
        _ = (2 * k) ^ 2 := by ring
    rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hsquare with heq | heq
    · exact heq
    ·
      have hleft0 : 0 ≤ dist first.1 second.1 := dist_nonneg
      have hright0 : 0 ≤ 2 * k := mul_nonneg (by norm_num) hk0
      nlinarith
  have hkD : k ≤ D / 2 := by
    have := blowUp_direction_dist_le first second
    dsimp [D]
    linarith
  have hδD : |δ| ≤ D / 2 := by
    have hs := blowUp_slope_sub_abs_le_dist first second
    dsimp [δ, s₁, s₂, D]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hformula :
      forwardBlowUpSq amplitude first -
          forwardBlowUpSq amplitude second =
        4 * amplitude * (σ * hy + δ * (my + amplitude * σ)) := by
    rw [forwardBlowUpSq_eq_unit_excess hfirst,
      forwardBlowUpSq_eq_unit_excess hsecond]
    dsimp [σ, δ, hy, my, s₁, s₂, y₁, y₂]
    ring
  have habsInner :
      |σ * hy + δ * (my + amplitude * σ)| ≤
        |σ| * |hy| + |δ| * (|my| + amplitude * |σ|) := by
    calc
      |σ * hy + δ * (my + amplitude * σ)| ≤
          |σ * hy| + |δ * (my + amplitude * σ)| := abs_add_le _ _
      _ = |σ| * |hy| + |δ| * |my + amplitude * σ| := by
        rw [abs_mul, abs_mul]
      _ ≤ |σ| * |hy| + |δ| * (|my| + amplitude * |σ|) := by
        exact add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left
            (calc
              |my + amplitude * σ| ≤ |my| + |amplitude * σ| := abs_add_le _ _
              _ = |my| + amplitude * |σ| := by
                rw [abs_mul, abs_of_nonneg ha0])
            (abs_nonneg δ))
  have hfirstTerm : |σ| * |hy| ≤
      (D / 2) * (|σ| * X) := by
    have hfactor0 : 0 ≤ |σ| * X := mul_nonneg (abs_nonneg _) hX0
    calc
      |σ| * |hy| = k * (|σ| * X) := by
        rw [show |hy| = k * X by simpa [hy] using hhy]
        ring
      _ ≤ (D / 2) * (|σ| * X) :=
        mul_le_mul_of_nonneg_right hkD hfactor0
  have hsecondFactor0 : 0 ≤ |my| + amplitude * |σ| :=
    add_nonneg (abs_nonneg _) (mul_nonneg ha0 (abs_nonneg _))
  have hsecondTerm : |δ| * (|my| + amplitude * |σ|) ≤
      (D / 2) * (r * Y + amplitude * |σ|) := by
    calc
      |δ| * (|my| + amplitude * |σ|) ≤
          (D / 2) * (|my| + amplitude * |σ|) :=
        mul_le_mul_of_nonneg_right hδD hsecondFactor0
      _ = (D / 2) * (r * Y + amplitude * |σ|) := by
        rw [show |my| = r * Y by simpa [my] using hmy]
  have hscaledInner :
      |σ * hy + δ * (my + amplitude * σ)| ≤
        (D / 2) * (r * Y + (X + amplitude) * W) := by
    calc
      |σ * hy + δ * (my + amplitude * σ)| ≤
          |σ| * |hy| + |δ| * (|my| + amplitude * |σ|) := habsInner
      _ ≤ (D / 2) * (|σ| * X) +
          (D / 2) * (r * Y + amplitude * |σ|) :=
        add_le_add hfirstTerm hsecondTerm
      _ = (D / 2) * (r * Y + (X + amplitude) * |σ|) := by ring
      _ ≤ (D / 2) * (r * Y + (X + amplitude) * W) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left hσW (add_nonneg hX0 ha0))
  have hcentered := centeredTwoPointEnvelope_le_exact ha0 hX0 hY0 hr0 hk0 hXY hrk
  have hcenteredEq :
      r * Y + (X + amplitude) * W =
        centeredTwoPointEnvelope amplitude X Y r k := by
    rfl
  rw [hformula, abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) ha0)]
  calc
    4 * amplitude * |σ * hy + δ * (my + amplitude * σ)| ≤
        4 * amplitude * ((D / 2) *
          (r * Y + (X + amplitude) * W)) :=
      mul_le_mul_of_nonneg_left hscaledInner (mul_nonneg (by norm_num) ha0)
    _ = (2 * amplitude *
          (r * Y + (X + amplitude) * W)) * D := by ring
    _ ≤ (2 * amplitude * exactTangentEnvelope amplitude) * D := by
      apply mul_le_mul_of_nonneg_right _ hD0
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) ha0)
      simpa [hcenteredEq] using hcentered
    _ = exactLocalTangentModulus amplitude * dist first second := by
      rfl

end BoundaryOfSelf.IntrinsicNonradialShearActualPairTransport
