import CircleAxisRounding

namespace BoundaryOfSelf
namespace OrbitCrossingLocalSegment

open UniformRadialBoundaryFamily
open InterpolatedBoundaryContour
open LocalPolygonalContour
open LocalSegmentRadialBound
open ConcreteRadialContourTraversal
open MinimalSeparatingContourOrbit
open ThresholdCutBond
open AxisThresholdSymmetry
open CircleAxisRounding
open LocalSegmentRealCompletion
open OneSidedEuclideanContourBound

/-!
IF-BS-22F-B3C1 extracts an actual local polygonal-contour segment from an
oriented threshold crossing carried by a global contour orbit. The state
already stores a cell-side incidence whose side crosses the threshold; this
incidence canonically supplies an active cell, a segment vertex, and its exact
interpolated crossing edge.
-/

def localSegmentOfState {m : Nat} (state : ContourState m) :
    LocalContourSegment m where
  cell := state.val.1
  active := by
    unfold ActiveCell
    exact List.length_pos_of_mem state.property

def segmentVertexOfState {m : Nat} (state : ContourState m) :
    SegmentVertex (localSegmentOfState state) :=
  ⟨state.val.2, state.property⟩

def segmentEdgeOfState {m : Nat} (state : ContourState m) : CrossingEdge m :=
  segmentEdge (localSegmentOfState state) (segmentVertexOfState state)

theorem segmentEdgeOfState_inner_eq {m : Nat}
    (state : ContourState m) (bridge : OrientedCrossing m)
    (represents : StateRepresentsBridge state bridge) :
    innerPoint (segmentEdgeOfState state) = bridge.insidePoint := by
  rcases represents with ⟨hInside, hOutside⟩ | ⟨hInside, hOutside⟩
  · have hStart := bridge.inside_has
    unfold Inside at hStart
    rw [hInside] at hStart
    change
      (if radialNumerator (sideStart state.val.1 state.val.2) <=
          thresholdNumerator m then
        sideStart state.val.1 state.val.2
      else sideEnd state.val.1 state.val.2) = bridge.insidePoint
    rw [if_pos hStart]
    exact hInside.symm
  · have hStart := bridge.outside_has
    unfold Inside at hStart
    rw [hOutside] at hStart
    change
      (if radialNumerator (sideStart state.val.1 state.val.2) <=
          thresholdNumerator m then
        sideStart state.val.1 state.val.2
      else sideEnd state.val.1 state.val.2) = bridge.insidePoint
    rw [if_neg hStart]
    exact hInside.symm

theorem segmentEdgeOfState_outer_eq {m : Nat}
    (state : ContourState m) (bridge : OrientedCrossing m)
    (represents : StateRepresentsBridge state bridge) :
    outerPoint (segmentEdgeOfState state) = bridge.outsidePoint := by
  rcases represents with ⟨hInside, hOutside⟩ | ⟨hInside, hOutside⟩
  · have hStart := bridge.inside_has
    unfold Inside at hStart
    rw [hInside] at hStart
    change
      (if radialNumerator (sideStart state.val.1 state.val.2) <=
          thresholdNumerator m then
        sideEnd state.val.1 state.val.2
      else sideStart state.val.1 state.val.2) = bridge.outsidePoint
    rw [if_pos hStart]
    exact hOutside.symm
  · have hStart := bridge.outside_has
    unfold Inside at hStart
    rw [hOutside] at hStart
    change
      (if radialNumerator (sideStart state.val.1 state.val.2) <=
          thresholdNumerator m then
        sideEnd state.val.1 state.val.2
      else sideStart state.val.1 state.val.2) = bridge.outsidePoint
    rw [if_neg hStart]
    exact hOutside.symm

structure OrbitLocalSegmentWitness {m : Nat}
    (orbit : ContourState m -> Prop) (bridge : OrientedCrossing m) where
  state : ContourState m
  state_mem : orbit state
  represents : StateRepresentsBridge state bridge
  inner_eq : innerPoint (segmentEdgeOfState state) = bridge.insidePoint
  outer_eq : outerPoint (segmentEdgeOfState state) = bridge.outsidePoint

theorem orbitCut_has_local_segment {m : Nat}
    {orbit : ContourState m -> Prop} {bridge : OrientedCrossing m}
    (membership : OrbitCut orbit bridge) :
    Nonempty (OrbitLocalSegmentWitness orbit bridge) := by
  rcases membership with ⟨state, stateMem, represents⟩
  exact ⟨{
    state := state
    state_mem := stateMem
    represents := represents
    inner_eq := segmentEdgeOfState_inner_eq state bridge represents
    outer_eq := segmentEdgeOfState_outer_eq state bridge represents
  }⟩

noncomputable def signFacingCrossing {m axis : Nat}
    (target : LocalSegmentRealCompletion.RealPlanePoint)
    (crossings : FourAxisCrossings m axis) : OrientedCrossing m :=
  if 0 <= target.x then crossings.right else crossings.left

theorem signFacingCrossing_axis {m axis : Nat}
    (target : LocalSegmentRealCompletion.RealPlanePoint)
    (crossings : FourAxisCrossings m axis) :
    (signFacingCrossing target crossings).insidePoint.y = axis /\
      (signFacingCrossing target crossings).outsidePoint.y = axis := by
  unfold signFacingCrossing
  split
  · exact ⟨crossings.right_inside_axis, crossings.right_outside_axis⟩
  · exact ⟨crossings.left_inside_axis, crossings.left_outside_axis⟩

theorem signFacingCrossing_direction {m axis : Nat}
    (target : LocalSegmentRealCompletion.RealPlanePoint)
    (crossings : FourAxisCrossings m axis) :
    (0 <= target.x /\
        (signFacingCrossing target crossings).outsidePoint.x =
          (signFacingCrossing target crossings).insidePoint.x + 1) \/
      (target.x < 0 /\
        (signFacingCrossing target crossings).outsidePoint.x + 1 =
          (signFacingCrossing target crossings).insidePoint.x) := by
  by_cases hSign : 0 <= target.x
  · left
    exact ⟨hSign, by simpa [signFacingCrossing, hSign] using crossings.right_advances⟩
  · right
    exact ⟨lt_of_not_ge hSign,
      by simpa [signFacingCrossing, hSign] using crossings.left_advances⟩

theorem signFacingCrossing_on_orbit {m axis : Nat}
    {orbit : ContourState m -> Prop}
    (target : LocalSegmentRealCompletion.RealPlanePoint)
    (crossings : FourAxisCrossings m axis)
    (rightMem : OrbitCut orbit crossings.right)
    (leftMem : OrbitCut orbit crossings.left) :
    OrbitCut orbit (signFacingCrossing target crossings) := by
  unfold signFacingCrossing
  split
  · exact rightMem
  · exact leftMem

theorem target_has_signFacing_local_segment_on_global_orbit {m : Nat}
    (hm : 0 < m) (anchor : ContourState m)
    (target : LocalSegmentRealCompletion.RealPlanePoint)
    (hTarget : OneSidedEuclideanContourBound.onTargetCircle target) :
    exists crossings : FourAxisCrossings m (targetAxis m target),
      Nonempty
        (OrbitLocalSegmentWitness
          (ContourOrbitPotentialSeparation.SelectedOrbit hm anchor)
          (signFacingCrossing target crossings)) := by
  rcases target_has_four_axis_crossings_on_global_orbit hm anchor target hTarget with
    ⟨crossings, rightMem, leftMem, topMem, bottomMem⟩
  refine ⟨crossings, orbitCut_has_local_segment ?_⟩
  exact signFacingCrossing_on_orbit target crossings rightMem leftMem

end OrbitCrossingLocalSegment
end BoundaryOfSelf

#print axioms BoundaryOfSelf.OrbitCrossingLocalSegment.segmentEdgeOfState_inner_eq
#print axioms BoundaryOfSelf.OrbitCrossingLocalSegment.segmentEdgeOfState_outer_eq
#print axioms BoundaryOfSelf.OrbitCrossingLocalSegment.orbitCut_has_local_segment
#print axioms BoundaryOfSelf.OrbitCrossingLocalSegment.signFacingCrossing_direction
#print axioms BoundaryOfSelf.OrbitCrossingLocalSegment.target_has_signFacing_local_segment_on_global_orbit
