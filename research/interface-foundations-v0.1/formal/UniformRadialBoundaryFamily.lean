import RefinedCurvedBoundaryGrid

namespace BoundaryOfSelf
namespace UniformRadialBoundaryFamily

open RationalBoundaryLimit
open RefinedCurvedBoundaryGrid

/-!
IF-BS-09 replaces a single exhausted grid by a family indexed by scale `m`.

Coordinates are integer numerators for the physical grid with spacing `1 / m`.
The sampled circle has centre `(2m, 2m)` and squared radius `2`, so its exact
integer threshold is `2m^2`.
-/

def radialGridSide (m : Nat) : Nat := 4 * m + 1

theorem radialGridSide_odd_shape (m : Nat) :
    radialGridSide m = 2 * (2 * m) + 1 := by
  simp [radialGridSide]
  omega

structure GridSample (m : Nat) where
  x : Nat
  y : Nat
  x_le : x <= 4 * m
  y_le : y <= 4 * m

def centerCoordinate (m : Nat) : Nat := 2 * m

def xOffset {m : Nat} (p : GridSample m) : Nat :=
  natDistance p.x (centerCoordinate m)

def yOffset {m : Nat} (p : GridSample m) : Nat :=
  natDistance p.y (centerCoordinate m)

def radialNumerator {m : Nat} (p : GridSample m) : Nat :=
  xOffset p * xOffset p + yOffset p * yOffset p

def thresholdNumerator (m : Nat) : Nat := 2 * m * m

def jumpBound (m : Nat) : Nat := 4 * m + 1

def UnitAdjacent {m : Nat} (p q : GridSample m) : Prop :=
  (p.y = q.y /\ (q.x = p.x + 1 \/ p.x = q.x + 1)) \/
  (p.x = q.x /\ (q.y = p.y + 1 \/ p.y = q.y + 1))

def Inside {m : Nat} (p : GridSample m) : Prop :=
  radialNumerator p <= thresholdNumerator m

def Crosses {m : Nat} (p q : GridSample m) : Prop :=
  (Inside p /\ ¬ Inside q) \/ (¬ Inside p /\ Inside q)

def WithinFieldBand {m : Nat} (p : GridSample m) (radius : Nat) : Prop :=
  radialNumerator p <= thresholdNumerator m + radius /\
  thresholdNumerator m <= radialNumerator p + radius

theorem xOffset_le_two_mul {m : Nat} (p : GridSample m) :
    xOffset p <= 2 * m := by
  have hxBound : p.x <= 4 * m := p.x_le
  have hx : p.x <= 2 * m + 2 * m := by omega
  unfold xOffset centerCoordinate natDistance
  split <;> omega

theorem yOffset_le_two_mul {m : Nat} (p : GridSample m) :
    yOffset p <= 2 * m := by
  have hyBound : p.y <= 4 * m := p.y_le
  have hy : p.y <= 2 * m + 2 * m := by omega
  unfold yOffset centerCoordinate natDistance
  split <;> omega

theorem natDistance_successor_near (a c : Nat) :
    natDistance (a + 1) c <= natDistance a c + 1 /\
    natDistance a c <= natDistance (a + 1) c + 1 := by
  unfold natDistance
  split <;> split <;> omega

private theorem successor_square (b : Nat) :
    (b + 1) * (b + 1) = b * b + 2 * b + 1 := by
  calc
    (b + 1) * (b + 1) = b * b + b + (b + 1) := by
      simp [Nat.add_mul, Nat.mul_add]
    _ = b * b + 2 * b + 1 := by omega

theorem square_step_bound {m a b : Nat}
    (ha : a <= 2 * m) (hab : a <= b + 1) :
    a * a <= b * b + jumpBound m := by
  by_cases hle : a <= b
  · have hsq : a * a <= b * b := Nat.mul_le_mul hle hle
    omega
  · have haeq : a = b + 1 := by omega
    subst a
    have hb : b <= 2 * m := by omega
    rw [successor_square]
    unfold jumpBound
    omega

theorem squares_within_jump {m a b : Nat}
    (ha : a <= 2 * m) (hb : b <= 2 * m)
    (hab : a <= b + 1) (hba : b <= a + 1) :
    a * a <= b * b + jumpBound m /\
    b * b <= a * a + jumpBound m := by
  exact ⟨square_step_bound ha hab, square_step_bound hb hba⟩

theorem adjacent_numerator_gap {m : Nat} (p q : GridSample m)
    (hAdjacent : UnitAdjacent p q) :
    radialNumerator p <= radialNumerator q + jumpBound m /\
    radialNumerator q <= radialNumerator p + jumpBound m := by
  rcases hAdjacent with ⟨hy, hx⟩ | ⟨hx, hy⟩
  · have hNear : xOffset p <= xOffset q + 1 /\
        xOffset q <= xOffset p + 1 := by
      rcases hx with hqx | hpq
      · have hs := natDistance_successor_near p.x (centerCoordinate m)
        constructor
        · simpa [xOffset, hqx] using hs.2
        · simpa [xOffset, hqx] using hs.1
      · have hs := natDistance_successor_near q.x (centerCoordinate m)
        constructor
        · simpa [xOffset, hpq] using hs.1
        · simpa [xOffset, hpq] using hs.2
    have hSquares := squares_within_jump
      (xOffset_le_two_mul p) (xOffset_le_two_mul q) hNear.1 hNear.2
    have hSame : yOffset p = yOffset q := by simp [yOffset, hy]
    constructor <;> unfold radialNumerator <;> rw [hSame] <;> omega
  · have hNear : yOffset p <= yOffset q + 1 /\
        yOffset q <= yOffset p + 1 := by
      rcases hy with hqy | hpy
      · have hs := natDistance_successor_near p.y (centerCoordinate m)
        constructor
        · simpa [yOffset, hqy] using hs.2
        · simpa [yOffset, hqy] using hs.1
      · have hs := natDistance_successor_near q.y (centerCoordinate m)
        constructor
        · simpa [yOffset, hpy] using hs.1
        · simpa [yOffset, hpy] using hs.2
    have hSquares := squares_within_jump
      (yOffset_le_two_mul p) (yOffset_le_two_mul q) hNear.1 hNear.2
    have hSame : xOffset p = xOffset q := by simp [xOffset, hx]
    constructor <;> unfold radialNumerator <;> rw [hSame] <;> omega

theorem crossing_within_jump_band {m : Nat} (p q : GridSample m)
    (hAdjacent : UnitAdjacent p q) (hCrosses : Crosses p q) :
    WithinFieldBand p (jumpBound m) /\
    WithinFieldBand q (jumpBound m) := by
  have hGap := adjacent_numerator_gap p q hAdjacent
  rcases hCrosses with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · unfold Inside at hp hq
    constructor <;> unfold WithinFieldBand <;> constructor <;> omega
  · unfold Inside at hp hq
    constructor <;> unfold WithinFieldBand <;> constructor <;> omega

theorem jumpBound_le_five_mul {m : Nat} (hm : 0 < m) :
    jumpBound m <= 5 * m := by
  unfold jumpBound
  omega

theorem crossing_within_five_cell_band {m : Nat} (hm : 0 < m)
    (p q : GridSample m) (hAdjacent : UnitAdjacent p q)
    (hCrosses : Crosses p q) :
    WithinFieldBand p (5 * m) /\ WithinFieldBand q (5 * m) := by
  have hBand := crossing_within_jump_band p q hAdjacent hCrosses
  have hBound := jumpBound_le_five_mul hm
  rcases hBand with ⟨⟨hpUpper, hpLower⟩, ⟨hqUpper, hqLower⟩⟩
  constructor <;> unfold WithinFieldBand <;> constructor <;> omega

def normalizedBandWidth (m : Nat) (hm : 0 < m) : PositiveFraction where
  numerator := 5
  denominator := m
  numerator_pos := by omega
  denominator_pos := hm

theorem normalized_band_limit :
    forall epsilon : PositiveFraction, exists N : Nat,
      0 < N /\ forall (m : Nat) (hm : 0 < m), N <= m ->
        FractionLt (normalizedBandWidth m hm) epsilon := by
  intro epsilon
  let N := 5 * epsilon.denominator + 1
  refine ⟨N, ?_, ?_⟩
  · dsimp [N]
    omega
  · intro m hm hNm
    unfold FractionLt normalizedBandWidth
    have hDen : 5 * epsilon.denominator < m := by
      dsimp [N] at hNm
      omega
    have hNum : 1 <= epsilon.numerator := by
      exact epsilon.numerator_pos
    have hScale : m <= epsilon.numerator * m := by
      calc
        m = 1 * m := by simp
        _ <= epsilon.numerator * m := Nat.mul_le_mul_right m hNum
    exact Nat.lt_of_lt_of_le hDen hScale

def fineSample (p : FineGridPoint) : GridSample 4 where
  x := p.x.val
  y := p.y.val
  x_le := by
    have hx := p.x.isLt
    omega
  y_le := by
    have hy := p.y.isLt
    omega

theorem scale_four_side : radialGridSide 4 = 17 := by native_decide

theorem fineSample_numerator (p : FineGridPoint) :
    radialNumerator (fineSample p) = fineScalarNumerator p := by
  rfl

end UniformRadialBoundaryFamily
end BoundaryOfSelf
