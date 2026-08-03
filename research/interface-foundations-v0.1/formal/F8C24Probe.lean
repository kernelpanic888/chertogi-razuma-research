import IntrinsicNonradialShearChordBridge

open BoundaryOfSelf.IntrinsicNonradialShearTangentEnvelope

#check scalarTangentDensity
#check FirstQuadrantUnit
#check scalarTangentDensity_le_exact
#check exactTangentEnvelope
#print BoundaryOfSelf.IntrinsicNonradialShearTangentEnvelope.FirstQuadrantUnit
#print BoundaryOfSelf.IntrinsicNonradialShearTangentEnvelope.scalarTangentDensity

namespace BoundaryOfSelf.IntrinsicNonradialShearCenteredEnvelope

open IntrinsicNonradialShearTangentEnvelope

/-- Worst centered two-point expression after absolute-value reduction.
`(X,Y)` records the absolute midpoint direction and `(r,k)` its midpoint/chord
radii, with both pairs constrained to the first-quadrant unit circle. -/
def centeredTwoPointEnvelope
    (amplitude X Y r k : ℝ) : ℝ :=
  r * Y + (X + amplitude) *
    (max (r * X) (k * Y) + max (r * Y) (k * X))

lemma unit_quadrant_coordinate_le_one
    {X Y : ℝ}
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hunit : X ^ 2 + Y ^ 2 = 1) :
    X ≤ 1 ∧ Y ≤ 1 := by
  constructor <;> nlinarith [sq_nonneg X, sq_nonneg Y]

lemma unit_quadrant_sum_le_sqrt_two
    {r k : ℝ}
    (hr0 : 0 ≤ r) (hk0 : 0 ≤ k)
    (hunit : r ^ 2 + k ^ 2 = 1) :
    r + k ≤ Real.sqrt 2 := by
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hsum0 : 0 ≤ r + k := add_nonneg hr0 hk0
  have hsumSq : (r + k) ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg (r - k)]
  nlinarith [sq_nonneg (Real.sqrt 2 - (r + k))]

lemma diagonal_coordinates_mem :
    (Real.sqrt 2 / 2, Real.sqrt 2 / 2) ∈ FirstQuadrantUnit := by
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hle : Real.sqrt 2 / 2 ≤ 1 := by nlinarith
  rw [FirstQuadrantUnit]
  refine ⟨⟨⟨by positivity, hle⟩, ⟨by positivity, hle⟩⟩, ?_⟩
  dsimp
  nlinarith

lemma mixed_x_base_bound
    {X Y : ℝ}
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hunit : X ^ 2 + Y ^ 2 = 1) :
    Y + Real.sqrt 2 * X ^ 2 ≤ 1 + Real.sqrt 2 / 2 := by
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hsqrtLower : (5 / 4 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [sq_nonneg (Real.sqrt 2 + 5 / 4)]
  nlinarith [sq_nonneg (Y - Real.sqrt 2 / 4)]

lemma mixed_y_base_bound
    {X Y : ℝ}
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hunit : X ^ 2 + Y ^ 2 = 1) :
    Y + Real.sqrt 2 * X * Y ≤ 1 + Real.sqrt 2 / 2 := by
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hY1 := (unit_quadrant_coordinate_le_one hX0 hY0 hunit).2
  have hxy : 2 * X * Y ≤ 1 := by
    nlinarith [sq_nonneg (X - Y)]
  have hmul : Real.sqrt 2 * X * Y ≤ Real.sqrt 2 / 2 := by
    nlinarith
  linarith

/-- Exact scalar optimization of the centered two-point chamber.  Every one of
the four midpoint/chord max-branches is bounded by the already attained local
tangent envelope. -/
theorem centeredTwoPointEnvelope_le_exact
    {amplitude X Y r k : ℝ}
    (ha0 : 0 ≤ amplitude)
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hr0 : 0 ≤ r) (hk0 : 0 ≤ k)
    (hXY : X ^ 2 + Y ^ 2 = 1)
    (hrk : r ^ 2 + k ^ 2 = 1) :
    centeredTwoPointEnvelope amplitude X Y r k ≤
      exactTangentEnvelope amplitude := by
  have hX1 := (unit_quadrant_coordinate_le_one hX0 hY0 hXY).1
  have hY1 := (unit_quadrant_coordinate_le_one hX0 hY0 hXY).2
  have hr1 := (unit_quadrant_coordinate_le_one hr0 hk0 hrk).1
  have hk1 := (unit_quadrant_coordinate_le_one hr0 hk0 hrk).2
  have hrk0 : 0 ≤ r + k := add_nonneg hr0 hk0
  have hrkUpper := unit_quadrant_sum_le_sqrt_two hr0 hk0 hrk
  have hsum0 : 0 ≤ X + Y := add_nonneg hX0 hY0
  have hXa0 : 0 ≤ X + amplitude := add_nonneg hX0 ha0
  have hcoordinates : (X, Y) ∈ FirstQuadrantUnit := by
    rw [FirstQuadrantUnit]
    exact ⟨⟨⟨hX0, hX1⟩, ⟨hY0, hY1⟩⟩, hXY⟩
  have hsame := scalarTangentDensity_le_exact amplitude hcoordinates
  have hsameValue :
      X * (X + Y) + Y + amplitude * (X + Y) ≤
        exactTangentEnvelope amplitude := by
    simpa [scalarTangentDensity] using hsame
  have hdiag := scalarTangentDensity_le_exact amplitude diagonal_coordinates_mem
  have hdiagValue :
      1 + Real.sqrt 2 / 2 + amplitude * Real.sqrt 2 ≤
        exactTangentEnvelope amplitude := by
    have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    rw [scalarTangentDensity] at hdiag
    dsimp at hdiag
    nlinarith
  rw [centeredTwoPointEnvelope]
  by_cases hfirst : k * Y ≤ r * X
  · rw [max_eq_left hfirst]
    by_cases hsecond : k * X ≤ r * Y
    · rw [max_eq_left hsecond]
      have hbase0 : 0 ≤ Y + (X + amplitude) * (X + Y) :=
        add_nonneg hY0 (mul_nonneg hXa0 hsum0)
      calc
        r * Y + (X + amplitude) * (r * X + r * Y) =
            r * (Y + (X + amplitude) * (X + Y)) := by ring
        _ ≤ 1 * (Y + (X + amplitude) * (X + Y)) :=
          mul_le_mul_of_nonneg_right hr1 hbase0
        _ = X * (X + Y) + Y + amplitude * (X + Y) := by ring
        _ ≤ exactTangentEnvelope amplitude := hsameValue
    · have hsecond' : r * Y ≤ k * X := le_of_lt (lt_of_not_ge hsecond)
      rw [max_eq_right hsecond']
      have hYpart : r * Y ≤ Y := by nlinarith
      have hXsq : X ^ 2 * (r + k) ≤ Real.sqrt 2 * X ^ 2 :=
        calc
          X ^ 2 * (r + k) = (r + k) * X ^ 2 := by ring
          _ ≤ Real.sqrt 2 * X ^ 2 :=
            mul_le_mul_of_nonneg_right hrkUpper (sq_nonneg X)
      have hXsum : X * (r + k) ≤ Real.sqrt 2 := by
        calc
          X * (r + k) ≤ 1 * Real.sqrt 2 :=
            mul_le_mul hX1 hrkUpper hrk0 (by norm_num)
          _ = Real.sqrt 2 := one_mul _
      have hmixed := mixed_x_base_bound hX0 hY0 hXY
      calc
        r * Y + (X + amplitude) * (r * X + k * X) =
            r * Y + X ^ 2 * (r + k) +
              amplitude * (X * (r + k)) := by ring
        _ ≤ Y + Real.sqrt 2 * X ^ 2 + amplitude * Real.sqrt 2 := by
          exact add_le_add
            (add_le_add hYpart hXsq)
            (mul_le_mul_of_nonneg_left hXsum ha0)
        _ ≤ 1 + Real.sqrt 2 / 2 + amplitude * Real.sqrt 2 := by linarith
        _ ≤ exactTangentEnvelope amplitude := hdiagValue
  · have hfirst' : r * X ≤ k * Y := le_of_lt (lt_of_not_ge hfirst)
    rw [max_eq_right hfirst']
    by_cases hsecond : k * X ≤ r * Y
    · rw [max_eq_left hsecond]
      have hYpart : r * Y ≤ Y := by nlinarith
      have hXYsum : X * Y * (r + k) ≤ Real.sqrt 2 * X * Y := by
        have hXY0 : 0 ≤ X * Y := mul_nonneg hX0 hY0
        nlinarith
      have hYsum : Y * (r + k) ≤ Real.sqrt 2 := by
        calc
          Y * (r + k) ≤ 1 * Real.sqrt 2 :=
            mul_le_mul hY1 hrkUpper hrk0 (by norm_num)
          _ = Real.sqrt 2 := one_mul _
      have hmixed := mixed_y_base_bound hX0 hY0 hXY
      calc
        r * Y + (X + amplitude) * (k * Y + r * Y) =
            r * Y + X * Y * (r + k) +
              amplitude * (Y * (r + k)) := by ring
        _ ≤ Y + Real.sqrt 2 * X * Y + amplitude * Real.sqrt 2 := by
          exact add_le_add
            (add_le_add hYpart hXYsum)
            (mul_le_mul_of_nonneg_left hYsum ha0)
        _ ≤ 1 + Real.sqrt 2 / 2 + amplitude * Real.sqrt 2 := by linarith
        _ ≤ exactTangentEnvelope amplitude := hdiagValue
    · have hsecond' : r * Y ≤ k * X := le_of_lt (lt_of_not_ge hsecond)
      rw [max_eq_right hsecond']
      have hYpart : r * Y ≤ Y := by nlinarith
      have hksum : k * (X + Y) ≤ X + Y :=
        (mul_le_mul_of_nonneg_right hk1 hsum0).trans_eq (one_mul _)
      calc
        r * Y + (X + amplitude) * (k * Y + k * X) =
            r * Y + (X + amplitude) * (k * (X + Y)) := by ring
        _ ≤ Y + (X + amplitude) * (X + Y) :=
          add_le_add hYpart (mul_le_mul_of_nonneg_left hksum hXa0)
        _ = X * (X + Y) + Y + amplitude * (X + Y) := by ring
        _ ≤ exactTangentEnvelope amplitude := hsameValue

theorem centeredTwoPointEnvelope_attains_exact
    {amplitude : ℝ}
    (_ha0 : 0 ≤ amplitude) :
    centeredTwoPointEnvelope amplitude
        (tangentEnvelopePoint amplitude).1
        (tangentEnvelopePoint amplitude).2 1 0 =
      exactTangentEnvelope amplitude := by
  have hpoint := tangentEnvelopePoint_mem amplitude
  have hX0 : 0 ≤ (tangentEnvelopePoint amplitude).1 := hpoint.1.1.1
  have hY0 : 0 ≤ (tangentEnvelopePoint amplitude).2 := hpoint.1.2.1
  rw [centeredTwoPointEnvelope,
    max_eq_left (by nlinarith : 0 * (tangentEnvelopePoint amplitude).2 ≤
      1 * (tangentEnvelopePoint amplitude).1),
    max_eq_left (by nlinarith : 0 * (tangentEnvelopePoint amplitude).1 ≤
      1 * (tangentEnvelopePoint amplitude).2),
    exactTangentEnvelope, scalarTangentDensity]
  ring

def CenteredEnvelopeValues (amplitude : ℝ) : Set ℝ :=
  {value | ∃ X Y r k : ℝ,
    0 ≤ X ∧ 0 ≤ Y ∧ 0 ≤ r ∧ 0 ≤ k ∧
    X ^ 2 + Y ^ 2 = 1 ∧ r ^ 2 + k ^ 2 = 1 ∧
    value = centeredTwoPointEnvelope amplitude X Y r k}

/-- The compact centered relaxation has exactly the same optimum as the local
tangent chamber.  No positive correction survives this scalar optimization. -/
theorem exactTangentEnvelope_isGreatest_centered
    {amplitude : ℝ}
    (ha0 : 0 ≤ amplitude) :
    IsGreatest (CenteredEnvelopeValues amplitude)
      (exactTangentEnvelope amplitude) := by
  constructor
  · have hpoint := tangentEnvelopePoint_mem amplitude
    refine ⟨(tangentEnvelopePoint amplitude).1,
      (tangentEnvelopePoint amplitude).2, 1, 0,
      hpoint.1.1.1, hpoint.1.2.1, by norm_num, by norm_num,
      hpoint.2, by norm_num, ?_⟩
    exact (centeredTwoPointEnvelope_attains_exact ha0).symm
  · intro value hvalue
    rcases hvalue with ⟨X, Y, r, k, hX0, hY0, hr0, hk0,
      hXY, hrk, rfl⟩
    exact centeredTwoPointEnvelope_le_exact ha0 hX0 hY0 hr0 hk0 hXY hrk

end BoundaryOfSelf.IntrinsicNonradialShearCenteredEnvelope
