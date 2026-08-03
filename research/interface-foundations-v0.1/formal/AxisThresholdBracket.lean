import FiniteRadialBoundaryTheorem
import ReverseCoverageMetricAdapter
import Mathlib.Tactic

namespace BoundaryOfSelf
namespace AxisThresholdBracket

open RefinedCurvedBoundaryGrid
open UniformRadialBoundaryFamily
open ThresholdCutBond


def rightScanSample (m y : ℕ) (hy : y ≤ 4 * m) (k : ℕ) : GridSample m where
  x := 2 * m + min k (2 * m)
  y := y
  x_le := by omega
  y_le := hy


theorem rightScanSample_zero (m y : ℕ) (hy : y ≤ 4 * m) :
    rightScanSample m y hy 0 =
      { x := 2 * m, y := y, x_le := by omega, y_le := hy } := by
  simp [rightScanSample]


theorem rightScanSample_boundary (m y : ℕ) (hy : y ≤ 4 * m) :
    rightScanSample m y hy (2 * m) =
      { x := 4 * m, y := y, x_le := by omega, y_le := hy } := by
  simp [rightScanSample]
  omega


theorem right_boundary_outside {m : ℕ} (hm : 0 < m)
    (y : ℕ) (hy : y ≤ 4 * m) :
    ¬ Inside (rightScanSample m y hy (2 * m)) := by
  intro hInside
  have hRight : ¬(2 * m + 2 * m ≤ 2 * m) := by omega
  unfold Inside radialNumerator thresholdNumerator xOffset yOffset
    centerCoordinate natDistance rightScanSample at hInside
  by_cases hRow : y ≤ 2 * m
  · simp [hRight, hRow] at hInside
    nlinarith
  · simp [hRight, hRow] at hInside
    nlinarith


theorem rightScanSample_adjacent_of_successor {m y : ℕ} (hy : y ≤ 4 * m)
    {k : ℕ} (hkPos : 0 < k) (hkLe : k ≤ 2 * m) :
    UnitAdjacent (rightScanSample m y hy (k - 1))
      (rightScanSample m y hy k) := by
  left
  constructor
  · rfl
  · left
    simp only [rightScanSample]
    rw [Nat.min_eq_left hkLe]
    rw [Nat.min_eq_left (le_trans (Nat.sub_le k 1) hkLe)]
    omega


structure RightRowBracket (m : ℕ) (y : ℕ) (hy : y ≤ 4 * m) where
  offset : ℕ
  offset_pos : 0 < offset
  offset_le : offset ≤ 2 * m
  inner_has : Inside (rightScanSample m y hy (offset - 1))
  outer_has : ¬ Inside (rightScanSample m y hy offset)


def RightRowBracket.edge {m y : ℕ} {hy : y ≤ 4 * m}
    (bracket : RightRowBracket m y hy) : OrientedCrossing m where
  insidePoint := rightScanSample m y hy (bracket.offset - 1)
  outsidePoint := rightScanSample m y hy bracket.offset
  adjacent := rightScanSample_adjacent_of_successor hy
    bracket.offset_pos bracket.offset_le
  inside_has := bracket.inner_has
  outside_has := bracket.outer_has


theorem exists_right_row_bracket {m : ℕ} (hm : 0 < m)
    (y : ℕ) (hy : y ≤ 4 * m)
    (centerInside : Inside (rightScanSample m y hy 0)) :
    Nonempty (RightRowBracket m y hy) := by
  classical
  let P : ℕ → Prop := fun k => ¬ Inside (rightScanSample m y hy k)
  have hBoundary : P (2 * m) := right_boundary_outside hm y hy
  have hExists : ∃ k, P k := ⟨2 * m, hBoundary⟩
  let k := Nat.find hExists
  have hkOuter : P k := Nat.find_spec hExists
  have hkLe : k ≤ 2 * m := Nat.find_min' hExists hBoundary
  have hkPos : 0 < k := by
    by_contra hNot
    have hkZero : k = 0 := Nat.eq_zero_of_not_pos hNot
    exact hkOuter (hkZero ▸ centerInside)
  have hkPredLt : k - 1 < k := by omega
  have hkInner : Inside (rightScanSample m y hy (k - 1)) := by
    by_contra hNot
    exact Nat.find_min hExists (by simpa [k] using hkPredLt) hNot
  exact ⟨{
    offset := k
    offset_pos := hkPos
    offset_le := hkLe
    inner_has := hkInner
    outer_has := hkOuter
  }⟩


theorem exists_right_row_oriented_crossing {m : ℕ} (hm : 0 < m)
    (y : ℕ) (hy : y ≤ 4 * m)
    (centerInside : Inside (rightScanSample m y hy 0)) :
    ∃ edge : OrientedCrossing m,
      edge.insidePoint.y = y ∧ edge.outsidePoint.y = y ∧
      edge.outsidePoint.x = edge.insidePoint.x + 1 ∧
      2 * m ≤ edge.insidePoint.x ∧ 2 * m ≤ edge.outsidePoint.x := by
  let bracket := Classical.choice (exists_right_row_bracket hm y hy centerInside)
  have hx : bracket.edge.outsidePoint.x = bracket.edge.insidePoint.x + 1 := by
    change 2 * m + min bracket.offset (2 * m) =
      (2 * m + min (bracket.offset - 1) (2 * m)) + 1
    rw [Nat.min_eq_left bracket.offset_le]
    rw [Nat.min_eq_left (le_trans (Nat.sub_le bracket.offset 1) bracket.offset_le)]
    have hPred : bracket.offset - 1 + 1 = bracket.offset :=
      Nat.sub_add_cancel (Nat.succ_le_iff.mpr bracket.offset_pos)
    calc
      2 * m + bracket.offset = 2 * m + (bracket.offset - 1 + 1) := by rw [hPred]
      _ = (2 * m + (bracket.offset - 1)) + 1 :=
        (Nat.add_assoc (2 * m) (bracket.offset - 1) 1).symm
  have hInsideCenter : 2 * m ≤ bracket.edge.insidePoint.x := by
    change 2 * m ≤ 2 * m + min (bracket.offset - 1) (2 * m)
    omega
  have hOutsideCenter : 2 * m ≤ bracket.edge.outsidePoint.x := by
    change 2 * m ≤ 2 * m + min bracket.offset (2 * m)
    omega
  exact ⟨bracket.edge, rfl, rfl, hx, hInsideCenter, hOutsideCenter⟩


theorem right_row_crossing_belongs_to_global_orbit {m : ℕ} (hm : 0 < m)
    (anchor : ConcreteRadialContourTraversal.ContourState m)
    (y : ℕ) (hy : y ≤ 4 * m)
    (centerInside : Inside (rightScanSample m y hy 0)) :
    ∃ edge : OrientedCrossing m,
      MinimalSeparatingContourOrbit.OrbitCut
        (ContourOrbitPotentialSeparation.SelectedOrbit hm anchor) edge := by
  obtain ⟨edge, _⟩ := exists_right_row_oriented_crossing hm y hy centerInside
  exact ⟨edge,
    FiniteRadialBoundaryTheorem.finite_radial_boundary_is_single_geometric_contour
      hm anchor edge⟩

end AxisThresholdBracket
end BoundaryOfSelf
