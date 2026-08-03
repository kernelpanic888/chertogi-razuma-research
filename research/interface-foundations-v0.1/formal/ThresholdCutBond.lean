import FiniteGridReachability

namespace BoundaryOfSelf
namespace ThresholdCutBond

open UniformRadialBoundaryFamily
open InterpolatedBoundaryContour
open LocalPolygonalContour
open FiniteGridReachability

/-!
IF-BS-19 proves that the complete threshold-crossing edge set is a bond in the
finite sampled grid. Removing every crossing edge separates inside from
outside. Restoring any one oriented crossing edge reconnects arbitrary points
on the two sides because each induced region is connected by IF-BS-18.
-/

inductive StepReachable {m : Nat}
    (Step : GridSample m -> GridSample m -> Prop) :
    GridSample m -> GridSample m -> Prop where
  | refl (point : GridSample m) : StepReachable Step point point
  | edge {left right : GridSample m}
      (step : Step left right) : StepReachable Step left right
  | trans {left middle right : GridSample m}
      (first : StepReachable Step left middle)
      (second : StepReachable Step middle right) :
      StepReachable Step left right

inductive NoncrossingStep {m : Nat} :
    GridSample m -> GridSample m -> Prop where
  | inside {left right : GridSample m}
      (adjacent : UnitAdjacent left right)
      (left_inside : Inside left) (right_inside : Inside right) :
      NoncrossingStep left right
  | outside {left right : GridSample m}
      (adjacent : UnitAdjacent left right)
      (left_outside : ¬ Inside left) (right_outside : ¬ Inside right) :
      NoncrossingStep left right

theorem noncrossingStep_inside_iff {m : Nat}
    {left right : GridSample m} (h : NoncrossingStep left right) :
    Inside left <-> Inside right := by
  cases h with
  | inside adjacent left_inside right_inside =>
      exact ⟨fun _ => right_inside, fun _ => left_inside⟩
  | outside adjacent left_outside right_outside =>
      constructor
      · intro hLeft
        exact False.elim (left_outside hLeft)
      · intro hRight
        exact False.elim (right_outside hRight)

theorem noncrossingReachable_inside_iff {m : Nat}
    {left right : GridSample m}
    (h : StepReachable NoncrossingStep left right) :
    Inside left <-> Inside right := by
  induction h with
  | refl point => exact Iff.rfl
  | edge step => exact noncrossingStep_inside_iff step
  | trans first second first_ih second_ih =>
      exact Iff.trans first_ih second_ih

theorem noncrossing_separates_sides {m : Nat}
    (insidePoint outsidePoint : GridSample m)
    (hInside : Inside insidePoint) (hOutside : ¬ Inside outsidePoint) :
    ¬ StepReachable NoncrossingStep insidePoint outsidePoint := by
  intro hReachable
  have hPreserved := noncrossingReachable_inside_iff hReachable
  exact hOutside (hPreserved.mp hInside)

structure OrientedCrossing (m : Nat) where
  insidePoint : GridSample m
  outsidePoint : GridSample m
  adjacent : UnitAdjacent insidePoint outsidePoint
  inside_has : Inside insidePoint
  outside_has : ¬ Inside outsidePoint

def IsOrientationOf {m : Nat} (bridge : OrientedCrossing m)
    (left right : GridSample m) : Prop :=
  (bridge.insidePoint = left /\ bridge.outsidePoint = right) \/
  (bridge.insidePoint = right /\ bridge.outsidePoint = left)

theorem crossing_is_orientable {m : Nat} (left right : GridSample m)
    (hAdjacent : UnitAdjacent left right) (hCrosses : Crosses left right) :
    exists bridge : OrientedCrossing m, IsOrientationOf bridge left right := by
  rcases hCrosses with ⟨hLeft, hRight⟩ | ⟨hLeft, hRight⟩
  · exact ⟨{
      insidePoint := left
      outsidePoint := right
      adjacent := hAdjacent
      inside_has := hLeft
      outside_has := hRight
    }, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨{
      insidePoint := right
      outsidePoint := left
      adjacent := unitAdjacent_comm hAdjacent
      inside_has := hRight
      outside_has := hLeft
    }, Or.inr ⟨rfl, rfl⟩⟩

noncomputable def orientCrossing {m : Nat} (left right : GridSample m)
    (hAdjacent : UnitAdjacent left right) (hCrosses : Crosses left right) :
    OrientedCrossing m :=
  Classical.choose (crossing_is_orientable left right hAdjacent hCrosses)

theorem orientCrossing_spec {m : Nat} (left right : GridSample m)
    (hAdjacent : UnitAdjacent left right) (hCrosses : Crosses left right) :
    IsOrientationOf
      (orientCrossing left right hAdjacent hCrosses) left right :=
  Classical.choose_spec
    (crossing_is_orientable left right hAdjacent hCrosses)

inductive BridgeStep {m : Nat} (bridge : OrientedCrossing m) :
    GridSample m -> GridSample m -> Prop where
  | inside {left right : GridSample m}
      (adjacent : UnitAdjacent left right)
      (left_inside : Inside left) (right_inside : Inside right) :
      BridgeStep bridge left right
  | outside {left right : GridSample m}
      (adjacent : UnitAdjacent left right)
      (left_outside : ¬ Inside left) (right_outside : ¬ Inside right) :
      BridgeStep bridge left right
  | forward : BridgeStep bridge bridge.insidePoint bridge.outsidePoint
  | backward : BridgeStep bridge bridge.outsidePoint bridge.insidePoint

theorem insideReachable_to_bridgeReachable {m : Nat}
    (bridge : OrientedCrossing m) {left right : GridSample m}
    (h : GridReachable Inside left right) :
    StepReachable (BridgeStep bridge) left right := by
  induction h with
  | refl point has =>
      exact StepReachable.refl point
  | edge left right left_has right_has adjacent =>
      exact StepReachable.edge
        (BridgeStep.inside adjacent left_has right_has)
  | trans left middle right first second first_ih second_ih =>
      exact StepReachable.trans first_ih second_ih

theorem outsideReachable_to_bridgeReachable {m : Nat}
    (bridge : OrientedCrossing m) {left right : GridSample m}
    (h : GridReachable (fun point => ¬ Inside point) left right) :
    StepReachable (BridgeStep bridge) left right := by
  induction h with
  | refl point has =>
      exact StepReachable.refl point
  | edge left right left_has right_has adjacent =>
      exact StepReachable.edge
        (BridgeStep.outside adjacent left_has right_has)
  | trans left middle right first second first_ih second_ih =>
      exact StepReachable.trans first_ih second_ih

theorem one_crossing_reconnects_sides {m : Nat} (hm : 0 < m)
    (bridge : OrientedCrossing m)
    (start finish : GridSample m)
    (hStart : Inside start) (hFinish : ¬ Inside finish) :
    StepReachable (BridgeStep bridge) start finish := by
  have hInsidePath : GridReachable Inside start bridge.insidePoint :=
    any_two_inside_samples_connected start bridge.insidePoint
      hStart bridge.inside_has
  have hOutsidePath :
      GridReachable (fun point => ¬ Inside point)
        bridge.outsidePoint finish :=
    any_two_outside_samples_connected hm bridge.outsidePoint finish
      bridge.outside_has hFinish
  exact StepReachable.trans
    (insideReachable_to_bridgeReachable bridge hInsidePath)
    (StepReachable.trans
      (StepReachable.edge (BridgeStep.forward (bridge := bridge)))
      (outsideReachable_to_bridgeReachable bridge hOutsidePath))

theorem raw_crossing_reconnects_sides {m : Nat} (hm : 0 < m)
    (left right : GridSample m)
    (hAdjacent : UnitAdjacent left right) (hCrosses : Crosses left right)
    (start finish : GridSample m)
    (hStart : Inside start) (hFinish : ¬ Inside finish) :
    IsOrientationOf (orientCrossing left right hAdjacent hCrosses) left right /\
      StepReachable
        (BridgeStep (orientCrossing left right hAdjacent hCrosses))
        start finish := by
  exact ⟨orientCrossing_spec left right hAdjacent hCrosses,
    one_crossing_reconnects_sides hm
      (orientCrossing left right hAdjacent hCrosses)
      start finish hStart hFinish⟩

structure ThresholdCutIsBond (m : Nat) where
  separates : forall insidePoint outsidePoint : GridSample m,
    Inside insidePoint -> ¬ Inside outsidePoint ->
    ¬ StepReachable NoncrossingStep insidePoint outsidePoint
  each_crossing_essential : forall bridge : OrientedCrossing m,
    forall start finish : GridSample m,
    Inside start -> ¬ Inside finish ->
    StepReachable (BridgeStep bridge) start finish

theorem radialThresholdCut_isBond {m : Nat} (hm : 0 < m) :
    ThresholdCutIsBond m where
  separates := noncrossing_separates_sides
  each_crossing_essential := one_crossing_reconnects_sides hm

end ThresholdCutBond
end BoundaryOfSelf
