import ContourOrbitGlobalMarking

namespace BoundaryOfSelf
namespace ContourOrbitPotentialSeparation

open UniformRadialBoundaryFamily
open InterpolatedBoundaryContour
open LocalPolygonalContour
open GlobalContourIncidence
open GlobalContourZeroBoundary
open FiniteGridReachability
open ConcreteRadialContourTraversal
open ThresholdCutBond
open MinimalSeparatingContourOrbit
open RectangularParityPotential
open ContourOrbitLocalParity
open ContourOrbitGlobalMarking

/-!
IF-BS-20E transports the global orbit potential to primal grid paths. Every
orbit-marked unit edge changes colour; every orbit-cut-avoiding step preserves
colour. The anchor orbit contains a crossing edge, and IF-BS-18 connects all
inside and outside samples to its endpoints. Hence the orbit cut separates the
two sides. IF-BS-20A minimality then forces the orbit to represent every
threshold crossing edge.
-/

def SelectedOrbit {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) : ContourState m -> Prop :=
  SameContourOrbit hm anchor

def OrbitGeometricMark {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (left right : GridSample m) : Prop :=
  exists state, SameContourOrbit hm anchor state /\
    SameUndirectedEdge
      (sideStart state.val.1 state.val.2)
      (sideEnd state.val.1 state.val.2) left right

theorem sameEdge_of_orientation {m : Nat} (bridge : OrientedCrossing m)
    (left right : GridSample m)
    (orientation : IsOrientationOf bridge left right) :
    SameUndirectedEdge left right bridge.insidePoint bridge.outsidePoint := by
  rcases orientation with ⟨inside_eq, outside_eq⟩ |
      ⟨inside_eq, outside_eq⟩
  · exact Or.inl ⟨inside_eq.symm, outside_eq.symm⟩
  · exact Or.inr ⟨outside_eq.symm, inside_eq.symm⟩

theorem orientation_of_sameEdge {m : Nat} (bridge : OrientedCrossing m)
    (left right : GridSample m)
    (same : SameUndirectedEdge left right
      bridge.insidePoint bridge.outsidePoint) :
    IsOrientationOf bridge left right := by
  rcases same with ⟨left_eq, right_eq⟩ | ⟨left_eq, right_eq⟩
  · exact Or.inl ⟨left_eq.symm, right_eq.symm⟩
  · exact Or.inr ⟨right_eq.symm, left_eq.symm⟩

theorem orbitCut_iff_geometricMark {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (bridge : OrientedCrossing m) :
    OrbitCut (SelectedOrbit hm anchor) bridge <->
      OrbitGeometricMark hm anchor bridge.insidePoint bridge.outsidePoint := by
  constructor
  · rintro ⟨state, state_orbit, represents⟩
    exact ⟨state, state_orbit, sameEdge_of_orientation bridge
      (sideStart state.val.1 state.val.2)
      (sideEnd state.val.1 state.val.2) represents⟩
  · rintro ⟨state, state_orbit, same⟩
    exact ⟨state, state_orbit, orientation_of_sameEdge bridge
      (sideStart state.val.1 state.val.2)
      (sideEnd state.val.1 state.val.2) same⟩

theorem sameUndirectedEdge_swap_right {m : Nat}
    {a b left right : GridSample m}
    (same : SameUndirectedEdge a b left right) :
    SameUndirectedEdge a b right left := by
  rcases same with ⟨a_left, b_right⟩ | ⟨a_right, b_left⟩
  · exact Or.inr ⟨a_left, b_right⟩
  · exact Or.inl ⟨a_right, b_left⟩

theorem orbitGeometricMark_comm {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (left right : GridSample m) :
    OrbitGeometricMark hm anchor left right <->
      OrbitGeometricMark hm anchor right left := by
  constructor <;> rintro ⟨state, state_orbit, same⟩ <;>
    exact ⟨state, state_orbit, sameUndirectedEdge_swap_right same⟩

theorem horizontal_mark_true_iff {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (edge : HorizontalGridEdge m) :
    (orbitRectangularMarking hm anchor).horizontal edge.x edge.y = true <->
      OrbitGeometricMark hm anchor (horizontalStart edge)
        (horizontalEnd edge) := by
  unfold orbitRectangularMarking
  rw [propBool_eq_true_iff]
  exact (horizontalCoordinateMarked_iff hm anchor edge).trans Iff.rfl

theorem vertical_mark_true_iff {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (edge : VerticalGridEdge m) :
    (orbitRectangularMarking hm anchor).vertical edge.x edge.y = true <->
      OrbitGeometricMark hm anchor (verticalStart edge)
        (verticalEnd edge) := by
  unfold orbitRectangularMarking
  rw [propBool_eq_true_iff]
  exact (verticalCoordinateMarked_iff hm anchor edge).trans Iff.rfl

theorem unitAdjacent_has_canonical_edge {m : Nat}
    (left right : GridSample m) (adjacent : UnitAdjacent left right) :
    (exists edge : HorizontalGridEdge m,
      left = horizontalStart edge /\ right = horizontalEnd edge) \/
    (exists edge : HorizontalGridEdge m,
      right = horizontalStart edge /\ left = horizontalEnd edge) \/
    (exists edge : VerticalGridEdge m,
      left = verticalStart edge /\ right = verticalEnd edge) \/
    (exists edge : VerticalGridEdge m,
      right = verticalStart edge /\ left = verticalEnd edge) := by
  rcases adjacent with ⟨same_row, forward | backward⟩ |
      ⟨same_column, upward | downward⟩
  · left
    let edge : HorizontalGridEdge m := {
      x := left.x
      y := left.y
      x_lt := by have h := right.x_le; omega
      y_le := left.y_le
    }
    refine ⟨edge, ?_, ?_⟩
    · apply gridSample_eq_of_coordinates <;>
        simp [edge, horizontalStart]
    · apply gridSample_eq_of_coordinates
      · simpa [edge, horizontalEnd] using forward
      · simpa [edge, horizontalEnd] using same_row.symm
  · right; left
    let edge : HorizontalGridEdge m := {
      x := right.x
      y := right.y
      x_lt := by have h := left.x_le; omega
      y_le := right.y_le
    }
    refine ⟨edge, ?_, ?_⟩
    · apply gridSample_eq_of_coordinates <;>
        simp [edge, horizontalStart]
    · apply gridSample_eq_of_coordinates
      · simpa [edge, horizontalEnd] using backward
      · simpa [edge, horizontalEnd] using same_row
  · right; right; left
    let edge : VerticalGridEdge m := {
      x := left.x
      y := left.y
      x_le := left.x_le
      y_lt := by have h := right.y_le; omega
    }
    refine ⟨edge, ?_, ?_⟩
    · apply gridSample_eq_of_coordinates <;>
        simp [edge, verticalStart]
    · apply gridSample_eq_of_coordinates
      · simpa [edge, verticalEnd] using same_column.symm
      · simpa [edge, verticalEnd] using upward
  · right; right; right
    let edge : VerticalGridEdge m := {
      x := right.x
      y := right.y
      x_le := right.x_le
      y_lt := by have h := left.y_le; omega
    }
    refine ⟨edge, ?_, ?_⟩
    · apply gridSample_eq_of_coordinates <;>
        simp [edge, verticalStart]
    · apply gridSample_eq_of_coordinates
      · simpa [edge, verticalEnd] using same_column
      · simpa [edge, verticalEnd] using downward

noncomputable def orbitGridColor {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (point : GridSample m) : Bool :=
  (orbitPotential hm anchor).color point.x point.y

theorem bxor_eq_false_iff_eq (left right : Bool) :
    bxor left right = false <-> left = right := by
  cases left <;> cases right <;> decide

theorem markedUnitAdjacent_endpoints_differ {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (left right : GridSample m)
    (adjacent : UnitAdjacent left right)
    (marked : OrbitGeometricMark hm anchor left right) :
    orbitGridColor hm anchor left ≠ orbitGridColor hm anchor right := by
  rcases unitAdjacent_has_canonical_edge left right adjacent with
      ⟨edge, left_eq, right_eq⟩ |
      ⟨edge, right_eq, left_eq⟩ |
      ⟨edge, left_eq, right_eq⟩ |
      ⟨edge, right_eq, left_eq⟩
  · subst left; subst right
    exact marked_horizontal_endpoints_differ (orbitPotential hm anchor)
      edge.x_lt edge.y_le ((horizontal_mark_true_iff hm anchor edge).mpr marked)
  · subst left; subst right
    have different := marked_horizontal_endpoints_differ
      (orbitPotential hm anchor) edge.x_lt edge.y_le
      ((horizontal_mark_true_iff hm anchor edge).mpr
        ((orbitGeometricMark_comm hm anchor _ _).mpr marked))
    exact fun same => different same.symm
  · subst left; subst right
    exact marked_vertical_endpoints_differ (orbitPotential hm anchor)
      edge.x_le edge.y_lt ((vertical_mark_true_iff hm anchor edge).mpr marked)
  · subst left; subst right
    have different := marked_vertical_endpoints_differ
      (orbitPotential hm anchor) edge.x_le edge.y_lt
      ((vertical_mark_true_iff hm anchor edge).mpr
        ((orbitGeometricMark_comm hm anchor _ _).mpr marked))
    exact fun same => different same.symm

theorem unmarkedUnitAdjacent_preserves_color {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (left right : GridSample m)
    (adjacent : UnitAdjacent left right)
    (unmarked : ¬ OrbitGeometricMark hm anchor left right) :
    orbitGridColor hm anchor left = orbitGridColor hm anchor right := by
  rcases unitAdjacent_has_canonical_edge left right adjacent with
      ⟨edge, left_eq, right_eq⟩ |
      ⟨edge, right_eq, left_eq⟩ |
      ⟨edge, left_eq, right_eq⟩ |
      ⟨edge, right_eq, left_eq⟩
  · subst left; subst right
    have mark_false :
        (orbitRectangularMarking hm anchor).horizontal edge.x edge.y = false := by
      cases mark_eq : (orbitRectangularMarking hm anchor).horizontal edge.x edge.y
      · rfl
      · exact False.elim (unmarked ((horizontal_mark_true_iff hm anchor edge).mp mark_eq))
    exact (bxor_eq_false_iff_eq _ _).mp
      ((orbitPotential hm anchor).horizontal_gradient
        edge.x edge.y edge.x_lt edge.y_le |>.trans mark_false)
  · subst left; subst right
    have unmarked_forward : ¬ OrbitGeometricMark hm anchor
        (horizontalStart edge) (horizontalEnd edge) := by
      intro has
      exact unmarked ((orbitGeometricMark_comm hm anchor _ _).mpr has)
    have mark_false :
        (orbitRectangularMarking hm anchor).horizontal edge.x edge.y = false := by
      cases mark_eq : (orbitRectangularMarking hm anchor).horizontal edge.x edge.y
      · rfl
      · exact False.elim
          (unmarked_forward ((horizontal_mark_true_iff hm anchor edge).mp mark_eq))
    have forward_eq := (bxor_eq_false_iff_eq _ _).mp
      ((orbitPotential hm anchor).horizontal_gradient
        edge.x edge.y edge.x_lt edge.y_le |>.trans mark_false)
    exact forward_eq.symm
  · subst left; subst right
    have mark_false :
        (orbitRectangularMarking hm anchor).vertical edge.x edge.y = false := by
      cases mark_eq : (orbitRectangularMarking hm anchor).vertical edge.x edge.y
      · rfl
      · exact False.elim (unmarked ((vertical_mark_true_iff hm anchor edge).mp mark_eq))
    exact (bxor_eq_false_iff_eq _ _).mp
      ((orbitPotential hm anchor).vertical_gradient
        edge.x edge.y edge.x_le edge.y_lt |>.trans mark_false)
  · subst left; subst right
    have unmarked_forward : ¬ OrbitGeometricMark hm anchor
        (verticalStart edge) (verticalEnd edge) := by
      intro has
      exact unmarked ((orbitGeometricMark_comm hm anchor _ _).mpr has)
    have mark_false :
        (orbitRectangularMarking hm anchor).vertical edge.x edge.y = false := by
      cases mark_eq : (orbitRectangularMarking hm anchor).vertical edge.x edge.y
      · rfl
      · exact False.elim
          (unmarked_forward ((vertical_mark_true_iff hm anchor edge).mp mark_eq))
    have forward_eq := (bxor_eq_false_iff_eq _ _).mp
      ((orbitPotential hm anchor).vertical_gradient
        edge.x edge.y edge.x_le edge.y_lt |>.trans mark_false)
    exact forward_eq.symm

theorem noncrossingStep_unmarked {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) {left right : GridSample m}
    (step : NoncrossingStep left right) :
    ¬ OrbitGeometricMark hm anchor left right := by
  intro marked
  rcases marked with ⟨state, _state_orbit, same⟩
  have crossing : Crosses left right :=
    crosses_of_sameUndirectedEdge (sameUndirectedEdge_symm same)
      (contourState_side_crosses state)
  cases step with
  | inside adjacent left_inside right_inside =>
      rcases crossing with ⟨_, right_outside⟩ | ⟨left_outside, _⟩
      · exact right_outside right_inside
      · exact left_outside left_inside
  | outside adjacent left_outside right_outside =>
      rcases crossing with ⟨left_inside, _⟩ | ⟨_, right_inside⟩
      · exact left_outside left_inside
      · exact right_outside right_inside

theorem cutAvoidingStep_unmarked {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) {left right : GridSample m}
    (step : CutAvoidingStep (OrbitCut (SelectedOrbit hm anchor)) left right) :
    ¬ OrbitGeometricMark hm anchor left right := by
  cases step with
  | noncrossing step =>
      exact noncrossingStep_unmarked hm anchor step
  | crossingForward bridge kept =>
      intro marked
      exact kept ((orbitCut_iff_geometricMark hm anchor bridge).mpr marked)
  | crossingBackward bridge kept =>
      intro marked
      have forwardMarked : OrbitGeometricMark hm anchor
          bridge.insidePoint bridge.outsidePoint :=
        (orbitGeometricMark_comm hm anchor _ _).mpr marked
      exact kept ((orbitCut_iff_geometricMark hm anchor bridge).mpr forwardMarked)

theorem cutAvoidingStep_adjacent {m : Nat}
    {removed : OrientedCrossing m -> Prop}
    {left right : GridSample m} (step : CutAvoidingStep removed left right) :
    UnitAdjacent left right := by
  cases step with
  | noncrossing step =>
      cases step with
      | inside adjacent _ _ => exact adjacent
      | outside adjacent _ _ => exact adjacent
  | crossingForward bridge kept => exact bridge.adjacent
  | crossingBackward bridge kept => exact unitAdjacent_comm bridge.adjacent

theorem cutAvoidingStep_preserves_color {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) {left right : GridSample m}
    (step : CutAvoidingStep (OrbitCut (SelectedOrbit hm anchor)) left right) :
    orbitGridColor hm anchor left = orbitGridColor hm anchor right := by
  exact unmarkedUnitAdjacent_preserves_color hm anchor left right
    (cutAvoidingStep_adjacent step) (cutAvoidingStep_unmarked hm anchor step)

theorem cutAvoidingReachable_preserves_color {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) {left right : GridSample m}
    (path : StepReachable
      (CutAvoidingStep (OrbitCut (SelectedOrbit hm anchor))) left right) :
    orbitGridColor hm anchor left = orbitGridColor hm anchor right := by
  induction path with
  | refl point => exact rfl
  | edge step => exact cutAvoidingStep_preserves_color hm anchor step
  | trans first second first_ih second_ih => exact first_ih.trans second_ih

theorem insideReachable_preserves_orbitColor {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) {left right : GridSample m}
    (path : GridReachable Inside left right) :
    orbitGridColor hm anchor left = orbitGridColor hm anchor right := by
  induction path with
  | refl point has => exact rfl
  | edge left right left_has right_has adjacent =>
      exact unmarkedUnitAdjacent_preserves_color hm anchor left right adjacent
        (noncrossingStep_unmarked hm anchor
          (NoncrossingStep.inside adjacent left_has right_has))
  | trans left middle right first second first_ih second_ih =>
      exact first_ih.trans second_ih

theorem outsideReachable_preserves_orbitColor {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) {left right : GridSample m}
    (path : GridReachable (fun point => ¬ Inside point) left right) :
    orbitGridColor hm anchor left = orbitGridColor hm anchor right := by
  induction path with
  | refl point has => exact rfl
  | edge left right left_has right_has adjacent =>
      exact unmarkedUnitAdjacent_preserves_color hm anchor left right adjacent
        (noncrossingStep_unmarked hm anchor
          (NoncrossingStep.outside adjacent left_has right_has))
  | trans left middle right first second first_ih second_ih =>
      exact first_ih.trans second_ih

theorem anchorBridge_is_in_orbitCut {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) :
    OrbitCut (SelectedOrbit hm anchor) (contourStateBridge anchor) := by
  exact ⟨anchor, SameContourOrbit.anchor,
    contourStateBridge_spec anchor⟩

theorem orbitSides_have_different_colors {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (insidePoint outsidePoint : GridSample m)
    (inside_has : Inside insidePoint) (outside_has : ¬ Inside outsidePoint) :
    orbitGridColor hm anchor insidePoint ≠
      orbitGridColor hm anchor outsidePoint := by
  let bridge := contourStateBridge anchor
  have bridge_marked : OrbitGeometricMark hm anchor
      bridge.insidePoint bridge.outsidePoint :=
    (orbitCut_iff_geometricMark hm anchor bridge).mp
      (anchorBridge_is_in_orbitCut hm anchor)
  have bridge_different : orbitGridColor hm anchor bridge.insidePoint ≠
      orbitGridColor hm anchor bridge.outsidePoint :=
    markedUnitAdjacent_endpoints_differ hm anchor
      bridge.insidePoint bridge.outsidePoint bridge.adjacent bridge_marked
  have inside_path : GridReachable Inside insidePoint bridge.insidePoint :=
    any_two_inside_samples_connected insidePoint bridge.insidePoint
      inside_has bridge.inside_has
  have outside_path : GridReachable (fun point => ¬ Inside point)
      bridge.outsidePoint outsidePoint :=
    any_two_outside_samples_connected hm bridge.outsidePoint outsidePoint
      bridge.outside_has outside_has
  have inside_color := insideReachable_preserves_orbitColor hm anchor inside_path
  have outside_color := outsideReachable_preserves_orbitColor hm anchor outside_path
  intro same
  apply bridge_different
  exact inside_color.symm.trans (same.trans outside_color.symm)

theorem contourOrbitCut_separates {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) :
    SeparatesSides (OrbitCut (SelectedOrbit hm anchor)) := by
  intro insidePoint outsidePoint inside_has outside_has path
  exact orbitSides_have_different_colors hm anchor
    insidePoint outsidePoint inside_has outside_has
    (cutAvoidingReachable_preserves_color hm anchor path)

theorem contourOrbitCut_is_full {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) :
    forall bridge : OrientedCrossing m,
      OrbitCut (SelectedOrbit hm anchor) bridge :=
  separating_contour_orbit_contains_every_crossing hm
    (SelectedOrbit hm anchor) (contourOrbitCut_separates hm anchor)

end ContourOrbitPotentialSeparation
end BoundaryOfSelf

#print axioms BoundaryOfSelf.ContourOrbitPotentialSeparation.unitAdjacent_has_canonical_edge
#print axioms BoundaryOfSelf.ContourOrbitPotentialSeparation.cutAvoidingStep_preserves_color
#print axioms BoundaryOfSelf.ContourOrbitPotentialSeparation.orbitSides_have_different_colors
#print axioms BoundaryOfSelf.ContourOrbitPotentialSeparation.contourOrbitCut_separates
#print axioms BoundaryOfSelf.ContourOrbitPotentialSeparation.contourOrbitCut_is_full
