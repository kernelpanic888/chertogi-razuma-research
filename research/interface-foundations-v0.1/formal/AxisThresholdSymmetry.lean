import AxisThresholdBracket

namespace BoundaryOfSelf
namespace AxisThresholdSymmetry

open RefinedCurvedBoundaryGrid
open UniformRadialBoundaryFamily
open ThresholdCutBond
open AxisThresholdBracket

/-!
IF-BS-22F-B2 transports the finite rightward threshold bracket of B1 through
two exact symmetries of the radial grid: reflection across the vertical centre
line and exchange of the two coordinates. Both maps preserve the radial
numerator, the inside predicate, and unit adjacency.
-/

def reflectX {m : Nat} (point : GridSample m) : GridSample m where
  x := 4 * m - point.x
  y := point.y
  x_le := Nat.sub_le _ _
  y_le := point.y_le

def swapAxes {m : Nat} (point : GridSample m) : GridSample m where
  x := point.y
  y := point.x
  x_le := point.y_le
  y_le := point.x_le

theorem natDistance_reflect_center {m x : Nat} (hx : x <= 4 * m) :
    natDistance (4 * m - x) (2 * m) = natDistance x (2 * m) := by
  unfold natDistance
  split <;> split <;> omega

theorem reflectX_involutive {m : Nat} (point : GridSample m) :
    reflectX (reflectX point) = point := by
  cases point with
  | mk x y hx hy =>
      simp [reflectX]
      omega

theorem swapAxes_involutive {m : Nat} (point : GridSample m) :
    swapAxes (swapAxes point) = point := by
  cases point <;> rfl

theorem reflectX_xOffset {m : Nat} (point : GridSample m) :
    xOffset (reflectX point) = xOffset point := by
  simpa [xOffset, centerCoordinate, reflectX] using
    (natDistance_reflect_center (m := m) point.x_le)

theorem reflectX_radialNumerator {m : Nat} (point : GridSample m) :
    radialNumerator (reflectX point) = radialNumerator point := by
  unfold radialNumerator
  rw [reflectX_xOffset]
  rfl

theorem swapAxes_radialNumerator {m : Nat} (point : GridSample m) :
    radialNumerator (swapAxes point) = radialNumerator point := by
  unfold radialNumerator xOffset yOffset
  simp only [swapAxes]
  omega

theorem reflectX_inside_iff {m : Nat} (point : GridSample m) :
    Inside (reflectX point) <-> Inside point := by
  simp only [Inside, reflectX_radialNumerator]

theorem swapAxes_inside_iff {m : Nat} (point : GridSample m) :
    Inside (swapAxes point) <-> Inside point := by
  simp only [Inside, swapAxes_radialNumerator]

theorem reflectX_unitAdjacent {m : Nat} {left right : GridSample m}
    (adjacent : UnitAdjacent left right) :
    UnitAdjacent (reflectX left) (reflectX right) := by
  rcases adjacent with
      ⟨sameY, rightStep | leftStep⟩ |
      ⟨sameX, upwardStep | downwardStep⟩
  · left
    refine ⟨sameY, Or.inr ?_⟩
    change 4 * m - left.x = (4 * m - right.x) + 1
    have hLeft := left.x_le
    have hRight := right.x_le
    omega
  · left
    refine ⟨sameY, Or.inl ?_⟩
    change 4 * m - right.x = (4 * m - left.x) + 1
    have hLeft := left.x_le
    have hRight := right.x_le
    omega
  · right
    refine ⟨?_, Or.inl upwardStep⟩
    change 4 * m - left.x = 4 * m - right.x
    omega
  · right
    refine ⟨?_, Or.inr downwardStep⟩
    change 4 * m - left.x = 4 * m - right.x
    omega

theorem swapAxes_unitAdjacent {m : Nat} {left right : GridSample m}
    (adjacent : UnitAdjacent left right) :
    UnitAdjacent (swapAxes left) (swapAxes right) := by
  rcases adjacent with ⟨sameY, stepX⟩ | ⟨sameX, stepY⟩
  · exact Or.inr ⟨sameY, stepX⟩
  · exact Or.inl ⟨sameX, stepY⟩

def reflectXCrossing {m : Nat} (edge : OrientedCrossing m) :
    OrientedCrossing m where
  insidePoint := reflectX edge.insidePoint
  outsidePoint := reflectX edge.outsidePoint
  adjacent := reflectX_unitAdjacent edge.adjacent
  inside_has := (reflectX_inside_iff edge.insidePoint).mpr edge.inside_has
  outside_has := fun outsideInside =>
    edge.outside_has
      ((reflectX_inside_iff edge.outsidePoint).mp outsideInside)

def swapAxesCrossing {m : Nat} (edge : OrientedCrossing m) :
    OrientedCrossing m where
  insidePoint := swapAxes edge.insidePoint
  outsidePoint := swapAxes edge.outsidePoint
  adjacent := swapAxes_unitAdjacent edge.adjacent
  inside_has := (swapAxes_inside_iff edge.insidePoint).mpr edge.inside_has
  outside_has := fun outsideInside =>
    edge.outside_has
      ((swapAxes_inside_iff edge.outsidePoint).mp outsideInside)

structure FourAxisCrossings (m axis : Nat) where
  right : OrientedCrossing m
  left : OrientedCrossing m
  top : OrientedCrossing m
  bottom : OrientedCrossing m
  right_inside_axis : right.insidePoint.y = axis
  right_outside_axis : right.outsidePoint.y = axis
  right_advances : right.outsidePoint.x = right.insidePoint.x + 1
  right_inside_center_le : 2 * m <= right.insidePoint.x
  right_outside_center_le : 2 * m <= right.outsidePoint.x
  left_inside_axis : left.insidePoint.y = axis
  left_outside_axis : left.outsidePoint.y = axis
  left_advances : left.outsidePoint.x + 1 = left.insidePoint.x
  left_inside_le_center : left.insidePoint.x <= 2 * m
  left_outside_le_center : left.outsidePoint.x <= 2 * m
  top_inside_axis : top.insidePoint.x = axis
  top_outside_axis : top.outsidePoint.x = axis
  top_advances : top.outsidePoint.y = top.insidePoint.y + 1
  top_inside_center_le : 2 * m <= top.insidePoint.y
  top_outside_center_le : 2 * m <= top.outsidePoint.y
  bottom_inside_axis : bottom.insidePoint.x = axis
  bottom_outside_axis : bottom.outsidePoint.x = axis
  bottom_advances : bottom.outsidePoint.y + 1 = bottom.insidePoint.y
  bottom_inside_le_center : bottom.insidePoint.y <= 2 * m
  bottom_outside_le_center : bottom.outsidePoint.y <= 2 * m

theorem exists_four_axis_crossings {m : Nat} (hm : 0 < m)
    (axis : Nat) (hAxis : axis <= 4 * m)
    (centerInside : Inside (rightScanSample m axis hAxis 0)) :
    Nonempty (FourAxisCrossings m axis) := by
  obtain ⟨right, rightInsideAxis, rightOutsideAxis, rightAdvances,
      rightInsideCenter, rightOutsideCenter⟩ :=
    exists_right_row_oriented_crossing hm axis hAxis centerInside
  have hInsideX := right.insidePoint.x_le
  have hOutsideX := right.outsidePoint.x_le
  refine ⟨{
    right := right
    left := reflectXCrossing right
    top := swapAxesCrossing right
    bottom := swapAxesCrossing (reflectXCrossing right)
    right_inside_axis := rightInsideAxis
    right_outside_axis := rightOutsideAxis
    right_advances := rightAdvances
    right_inside_center_le := rightInsideCenter
    right_outside_center_le := rightOutsideCenter
    left_inside_axis := ?_
    left_outside_axis := ?_
    left_advances := ?_
    left_inside_le_center := ?_
    left_outside_le_center := ?_
    top_inside_axis := ?_
    top_outside_axis := ?_
    top_advances := ?_
    top_inside_center_le := ?_
    top_outside_center_le := ?_
    bottom_inside_axis := ?_
    bottom_outside_axis := ?_
    bottom_advances := ?_
    bottom_inside_le_center := ?_
    bottom_outside_le_center := ?_
  }⟩
  · exact rightInsideAxis
  · exact rightOutsideAxis
  · change 4 * m - right.outsidePoint.x + 1 =
      4 * m - right.insidePoint.x
    omega
  · change 4 * m - right.insidePoint.x <= 2 * m
    omega
  · change 4 * m - right.outsidePoint.x <= 2 * m
    omega
  · exact rightInsideAxis
  · exact rightOutsideAxis
  · exact rightAdvances
  · exact rightInsideCenter
  · exact rightOutsideCenter
  · exact rightInsideAxis
  · exact rightOutsideAxis
  · change 4 * m - right.outsidePoint.x + 1 =
      4 * m - right.insidePoint.x
    omega
  · change 4 * m - right.insidePoint.x <= 2 * m
    omega
  · change 4 * m - right.outsidePoint.x <= 2 * m
    omega

theorem four_axis_crossings_belong_to_global_orbit {m axis : Nat}
    (hm : 0 < m)
    (anchor : ConcreteRadialContourTraversal.ContourState m)
    (crossings : FourAxisCrossings m axis) :
    MinimalSeparatingContourOrbit.OrbitCut
        (ContourOrbitPotentialSeparation.SelectedOrbit hm anchor)
        crossings.right ∧
      MinimalSeparatingContourOrbit.OrbitCut
        (ContourOrbitPotentialSeparation.SelectedOrbit hm anchor)
        crossings.left ∧
      MinimalSeparatingContourOrbit.OrbitCut
        (ContourOrbitPotentialSeparation.SelectedOrbit hm anchor)
        crossings.top ∧
      MinimalSeparatingContourOrbit.OrbitCut
        (ContourOrbitPotentialSeparation.SelectedOrbit hm anchor)
        crossings.bottom := by
  constructor
  · exact FiniteRadialBoundaryTheorem.finite_radial_boundary_is_single_geometric_contour
      hm anchor crossings.right
  constructor
  · exact FiniteRadialBoundaryTheorem.finite_radial_boundary_is_single_geometric_contour
      hm anchor crossings.left
  constructor
  · exact FiniteRadialBoundaryTheorem.finite_radial_boundary_is_single_geometric_contour
      hm anchor crossings.top
  · exact FiniteRadialBoundaryTheorem.finite_radial_boundary_is_single_geometric_contour
      hm anchor crossings.bottom

theorem exists_four_axis_crossings_on_global_orbit {m : Nat} (hm : 0 < m)
    (anchor : ConcreteRadialContourTraversal.ContourState m)
    (axis : Nat) (hAxis : axis <= 4 * m)
    (centerInside : Inside (rightScanSample m axis hAxis 0)) :
    exists crossings : FourAxisCrossings m axis,
      MinimalSeparatingContourOrbit.OrbitCut
          (ContourOrbitPotentialSeparation.SelectedOrbit hm anchor)
          crossings.right ∧
        MinimalSeparatingContourOrbit.OrbitCut
          (ContourOrbitPotentialSeparation.SelectedOrbit hm anchor)
          crossings.left ∧
        MinimalSeparatingContourOrbit.OrbitCut
          (ContourOrbitPotentialSeparation.SelectedOrbit hm anchor)
          crossings.top ∧
        MinimalSeparatingContourOrbit.OrbitCut
          (ContourOrbitPotentialSeparation.SelectedOrbit hm anchor)
          crossings.bottom := by
  obtain ⟨crossings⟩ := exists_four_axis_crossings hm axis hAxis centerInside
  exact ⟨crossings, four_axis_crossings_belong_to_global_orbit hm anchor crossings⟩

end AxisThresholdSymmetry
end BoundaryOfSelf

#print axioms BoundaryOfSelf.AxisThresholdSymmetry.reflectX_involutive
#print axioms BoundaryOfSelf.AxisThresholdSymmetry.reflectX_radialNumerator
#print axioms BoundaryOfSelf.AxisThresholdSymmetry.swapAxes_radialNumerator
#print axioms BoundaryOfSelf.AxisThresholdSymmetry.reflectX_unitAdjacent
#print axioms BoundaryOfSelf.AxisThresholdSymmetry.swapAxes_unitAdjacent
#print axioms BoundaryOfSelf.AxisThresholdSymmetry.exists_four_axis_crossings
#print axioms BoundaryOfSelf.AxisThresholdSymmetry.exists_four_axis_crossings_on_global_orbit
