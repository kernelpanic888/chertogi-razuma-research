import ThresholdCutBond
import ConcreteRadialContourTraversal

namespace BoundaryOfSelf
namespace MinimalSeparatingContourOrbit

open UniformRadialBoundaryFamily
open LocalPolygonalContour
open FiniteAlternatingCycleKernel
open ConcreteRadialContourTraversal
open ThresholdCutBond

/-!
IF-BS-20A turns the edge-essentiality statement of IF-BS-19 into an
inclusion-minimality theorem. It also supplies the typed map from IF-BS-15
contour states to the crossing edges represented by their cell sides.
-/

inductive CutAvoidingStep {m : Nat}
    (removed : OrientedCrossing m -> Prop) :
    GridSample m -> GridSample m -> Prop where
  | noncrossing {left right : GridSample m}
      (step : NoncrossingStep left right) :
      CutAvoidingStep removed left right
  | crossingForward (bridge : OrientedCrossing m)
      (kept : ¬ removed bridge) :
      CutAvoidingStep removed bridge.insidePoint bridge.outsidePoint
  | crossingBackward (bridge : OrientedCrossing m)
      (kept : ¬ removed bridge) :
      CutAvoidingStep removed bridge.outsidePoint bridge.insidePoint

def SeparatesSides {m : Nat}
    (removed : OrientedCrossing m -> Prop) : Prop :=
  forall insidePoint outsidePoint : GridSample m,
    Inside insidePoint -> ¬ Inside outsidePoint ->
    ¬ StepReachable (CutAvoidingStep removed) insidePoint outsidePoint

theorem bridgeStep_to_cutAvoidingStep {m : Nat}
    {removed : OrientedCrossing m -> Prop}
    (bridge : OrientedCrossing m) (kept : ¬ removed bridge)
    {left right : GridSample m} (step : BridgeStep bridge left right) :
    CutAvoidingStep removed left right := by
  cases step with
  | inside adjacent left_inside right_inside =>
      exact CutAvoidingStep.noncrossing
        (NoncrossingStep.inside adjacent left_inside right_inside)
  | outside adjacent left_outside right_outside =>
      exact CutAvoidingStep.noncrossing
        (NoncrossingStep.outside adjacent left_outside right_outside)
  | forward =>
      exact CutAvoidingStep.crossingForward bridge kept
  | backward =>
      exact CutAvoidingStep.crossingBackward bridge kept

theorem bridgeReachable_to_cutAvoidingReachable {m : Nat}
    {removed : OrientedCrossing m -> Prop}
    (bridge : OrientedCrossing m) (kept : ¬ removed bridge)
    {left right : GridSample m}
    (path : StepReachable (BridgeStep bridge) left right) :
    StepReachable (CutAvoidingStep removed) left right := by
  induction path with
  | refl point =>
      exact StepReachable.refl point
  | edge step =>
      exact StepReachable.edge
        (bridgeStep_to_cutAvoidingStep bridge kept step)
  | trans first second first_ih second_ih =>
      exact StepReachable.trans first_ih second_ih

theorem separating_subcut_contains_every_crossing {m : Nat}
    (hm : 0 < m) (removed : OrientedCrossing m -> Prop)
    (separates : SeparatesSides removed) :
    forall bridge : OrientedCrossing m, removed bridge := by
  intro bridge
  apply Classical.byContradiction
  intro kept
  have bridgePath : StepReachable (BridgeStep bridge)
      bridge.insidePoint bridge.outsidePoint :=
    one_crossing_reconnects_sides hm bridge
      bridge.insidePoint bridge.outsidePoint
      bridge.inside_has bridge.outside_has
  have avoidingPath : StepReachable (CutAvoidingStep removed)
      bridge.insidePoint bridge.outsidePoint :=
    bridgeReachable_to_cutAvoidingReachable bridge kept bridgePath
  exact separates bridge.insidePoint bridge.outsidePoint
    bridge.inside_has bridge.outside_has avoidingPath

def FullThresholdCut {m : Nat} : OrientedCrossing m -> Prop :=
  fun _ => True

theorem fullCutAvoidingStep_is_noncrossing {m : Nat}
    {left right : GridSample m}
    (step : CutAvoidingStep FullThresholdCut left right) :
    NoncrossingStep left right := by
  cases step with
  | noncrossing noncrossing =>
      exact noncrossing
  | crossingForward bridge kept =>
      exact False.elim (kept True.intro)
  | crossingBackward bridge kept =>
      exact False.elim (kept True.intro)

theorem fullCutAvoidingReachable_is_noncrossing {m : Nat}
    {left right : GridSample m}
    (path : StepReachable (CutAvoidingStep FullThresholdCut) left right) :
    StepReachable NoncrossingStep left right := by
  induction path with
  | refl point =>
      exact StepReachable.refl point
  | edge step =>
      exact StepReachable.edge (fullCutAvoidingStep_is_noncrossing step)
  | trans first second first_ih second_ih =>
      exact StepReachable.trans first_ih second_ih

theorem fullThresholdCut_separates {m : Nat} :
    SeparatesSides (FullThresholdCut (m := m)) := by
  intro insidePoint outsidePoint inside_has outside_has path
  exact noncrossing_separates_sides insidePoint outsidePoint
    inside_has outside_has
    (fullCutAvoidingReachable_is_noncrossing path)

structure InclusionMinimalThresholdCut (m : Nat) : Prop where
  full_separates : SeparatesSides (FullThresholdCut (m := m))
  every_separator_is_full : forall removed : OrientedCrossing m -> Prop,
    SeparatesSides removed -> forall bridge, removed bridge

theorem radialThresholdCut_isInclusionMinimal {m : Nat} (hm : 0 < m) :
    InclusionMinimalThresholdCut m where
  full_separates := fullThresholdCut_separates
  every_separator_is_full :=
    separating_subcut_contains_every_crossing hm

theorem contourState_side_crosses {m : Nat} (state : ContourState m) :
    Crosses
      (sideStart state.val.1 state.val.2)
      (sideEnd state.val.1 state.val.2) := by
  exact (sideCrossingFlag_eq_true_iff state.val.1 state.val.2).mp
    ((mem_crossingSides_iff state.val.1 state.val.2).mp state.property)

noncomputable def contourStateBridge {m : Nat} (state : ContourState m) :
    OrientedCrossing m :=
  orientCrossing
    (sideStart state.val.1 state.val.2)
    (sideEnd state.val.1 state.val.2)
    (side_adjacent state.val.1 state.val.2)
    (contourState_side_crosses state)

def StateRepresentsBridge {m : Nat}
    (state : ContourState m) (bridge : OrientedCrossing m) : Prop :=
  IsOrientationOf bridge
    (sideStart state.val.1 state.val.2)
    (sideEnd state.val.1 state.val.2)

theorem contourStateBridge_spec {m : Nat} (state : ContourState m) :
    StateRepresentsBridge state (contourStateBridge state) := by
  exact orientCrossing_spec
    (sideStart state.val.1 state.val.2)
    (sideEnd state.val.1 state.val.2)
    (side_adjacent state.val.1 state.val.2)
    (contourState_side_crosses state)

def OrbitCut {m : Nat} (orbit : ContourState m -> Prop) :
    OrientedCrossing m -> Prop :=
  fun bridge => exists state, orbit state /\ StateRepresentsBridge state bridge

theorem separating_contour_orbit_contains_every_crossing {m : Nat}
    (hm : 0 < m) (orbit : ContourState m -> Prop)
    (separates : SeparatesSides (OrbitCut orbit)) :
    forall bridge : OrientedCrossing m, OrbitCut orbit bridge :=
  separating_subcut_contains_every_crossing hm (OrbitCut orbit) separates

end MinimalSeparatingContourOrbit
end BoundaryOfSelf

#print axioms BoundaryOfSelf.MinimalSeparatingContourOrbit.separating_subcut_contains_every_crossing
#print axioms BoundaryOfSelf.MinimalSeparatingContourOrbit.fullThresholdCut_separates
#print axioms BoundaryOfSelf.MinimalSeparatingContourOrbit.radialThresholdCut_isInclusionMinimal
#print axioms BoundaryOfSelf.MinimalSeparatingContourOrbit.contourStateBridge_spec
#print axioms BoundaryOfSelf.MinimalSeparatingContourOrbit.separating_contour_orbit_contains_every_crossing
