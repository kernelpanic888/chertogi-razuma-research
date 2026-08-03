import OrbitCrossingLocalSegment

namespace BoundaryOfSelf
namespace DominantAxisLocalSegment

noncomputable section

open LocalSegmentRealCompletion
open OneSidedEuclideanContourBound
open ConcreteRadialContourTraversal
open MinimalSeparatingContourOrbit
open AxisThresholdSymmetry
open CircleAxisRounding
open OrbitCrossingLocalSegment

/-!
IF-BS-22F-B3C2A removes the pole singularity of a horizontal-only selector.
When |x| dominates, the target uses a right/left crossing on the inward-rounded
y row. When |y| dominates, the swapped target supplies an inward-rounded x
column and the selector uses its top/bottom crossing. Both branches stay on the
same selected global contour orbit and therefore produce a local segment.
-/

def swapTarget (target : RealPlanePoint) : RealPlanePoint :=
  { x := target.y, y := target.x }

@[simp] theorem swapTarget_x (target : RealPlanePoint) :
    (swapTarget target).x = target.y := rfl

@[simp] theorem swapTarget_y (target : RealPlanePoint) :
    (swapTarget target).y = target.x := rfl

@[simp] theorem swapTarget_swapTarget (target : RealPlanePoint) :
    swapTarget (swapTarget target) = target := by
  ext <;> rfl

theorem swapTarget_onTargetCircle {target : RealPlanePoint}
    (hTarget : onTargetCircle target) :
    onTargetCircle (swapTarget target) := by
  unfold onTargetCircle squaredRadius at hTarget ⊢
  simp only [swapTarget_x, swapTarget_y]
  nlinarith

def verticalFacingCrossing {m axis : Nat} (target : RealPlanePoint)
    (crossings : FourAxisCrossings m axis) :=
  if 0 <= target.y then crossings.top else crossings.bottom

theorem verticalFacingCrossing_axis {m axis : Nat} (target : RealPlanePoint)
    (crossings : FourAxisCrossings m axis) :
    (verticalFacingCrossing target crossings).insidePoint.x = axis /\
      (verticalFacingCrossing target crossings).outsidePoint.x = axis := by
  unfold verticalFacingCrossing
  split
  · exact ⟨crossings.top_inside_axis, crossings.top_outside_axis⟩
  · exact ⟨crossings.bottom_inside_axis, crossings.bottom_outside_axis⟩

theorem verticalFacingCrossing_direction {m axis : Nat}
    (target : RealPlanePoint) (crossings : FourAxisCrossings m axis) :
    (0 <= target.y /\
        (verticalFacingCrossing target crossings).outsidePoint.y =
          (verticalFacingCrossing target crossings).insidePoint.y + 1) \/
      (target.y < 0 /\
        (verticalFacingCrossing target crossings).outsidePoint.y + 1 =
          (verticalFacingCrossing target crossings).insidePoint.y) := by
  by_cases hSign : 0 <= target.y
  · left
    exact ⟨hSign,
      by simpa [verticalFacingCrossing, hSign] using crossings.top_advances⟩
  · right
    exact ⟨lt_of_not_ge hSign,
      by simpa [verticalFacingCrossing, hSign] using crossings.bottom_advances⟩

def dominantFacingCrossing {m horizontalAxis verticalAxis : Nat}
    (target : RealPlanePoint)
    (horizontal : FourAxisCrossings m horizontalAxis)
    (vertical : FourAxisCrossings m verticalAxis) :=
  if |target.y| <= |target.x| then
    signFacingCrossing target horizontal
  else
    verticalFacingCrossing target vertical

theorem dominantFacingCrossing_is_horizontal_or_vertical
    {m horizontalAxis verticalAxis : Nat} (target : RealPlanePoint)
    (horizontal : FourAxisCrossings m horizontalAxis)
    (vertical : FourAxisCrossings m verticalAxis) :
    dominantFacingCrossing target horizontal vertical =
        signFacingCrossing target horizontal \/
      dominantFacingCrossing target horizontal vertical =
        verticalFacingCrossing target vertical := by
  unfold dominantFacingCrossing
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem dominantFacingCrossing_on_orbit
    {m horizontalAxis verticalAxis : Nat}
    {orbit : ContourState m -> Prop} (target : RealPlanePoint)
    (horizontal : FourAxisCrossings m horizontalAxis)
    (vertical : FourAxisCrossings m verticalAxis)
    (horizontalRight : OrbitCut orbit horizontal.right)
    (horizontalLeft : OrbitCut orbit horizontal.left)
    (verticalTop : OrbitCut orbit vertical.top)
    (verticalBottom : OrbitCut orbit vertical.bottom) :
    OrbitCut orbit (dominantFacingCrossing target horizontal vertical) := by
  unfold dominantFacingCrossing
  split
  · exact signFacingCrossing_on_orbit target horizontal
      horizontalRight horizontalLeft
  · unfold verticalFacingCrossing
    split
    · exact verticalTop
    · exact verticalBottom

theorem target_has_dominant_local_segment_on_global_orbit {m : Nat}
    (hm : 0 < m) (anchor : ContourState m)
    (target : RealPlanePoint) (hTarget : onTargetCircle target) :
    exists
      (horizontal : FourAxisCrossings m (targetAxis m target))
      (vertical : FourAxisCrossings m (targetAxis m (swapTarget target))),
      Nonempty
        (OrbitLocalSegmentWitness
          (ContourOrbitPotentialSeparation.SelectedOrbit hm anchor)
          (dominantFacingCrossing target horizontal vertical)) := by
  rcases target_has_four_axis_crossings_on_global_orbit hm anchor target hTarget with
    ⟨horizontal, horizontalRight, horizontalLeft,
      horizontalTop, horizontalBottom⟩
  have hSwap : onTargetCircle (swapTarget target) :=
    swapTarget_onTargetCircle hTarget
  rcases target_has_four_axis_crossings_on_global_orbit hm anchor
      (swapTarget target) hSwap with
    ⟨vertical, verticalRight, verticalLeft, verticalTop, verticalBottom⟩
  refine ⟨horizontal, vertical, orbitCut_has_local_segment ?_⟩
  exact dominantFacingCrossing_on_orbit target horizontal vertical
    horizontalRight horizontalLeft verticalTop verticalBottom

end
end DominantAxisLocalSegment
end BoundaryOfSelf

#print axioms BoundaryOfSelf.DominantAxisLocalSegment.swapTarget_onTargetCircle
#print axioms BoundaryOfSelf.DominantAxisLocalSegment.verticalFacingCrossing_direction
#print axioms BoundaryOfSelf.DominantAxisLocalSegment.dominantFacingCrossing_on_orbit
#print axioms BoundaryOfSelf.DominantAxisLocalSegment.target_has_dominant_local_segment_on_global_orbit
