import CrossingInterpolationPhysicalBridge

namespace BoundaryOfSelf
namespace DominantBranchCoordinateBound

noncomputable section

open UniformRadialBoundaryFamily
open InterpolatedBoundaryContour
open LocalSegmentRealCompletion
open OneSidedEuclideanContourBound
open AxisThresholdSymmetry
open CircleAxisRounding
open DominantAxisLocalSegment
open DominantCoordinateMetricPrelude
open GridPhysicalCoordinateAdapter
open CrossingInterpolationPhysicalBridge

private theorem physicalX_nonneg_of_center_le {m : Nat} (hm : 0 < m)
    (sample : GridSample m) (hCenter : 2 * m <= sample.x) :
    0 <= physicalX sample := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hCast : (2 : Real) * (m : Real) <= (sample.x : Real) := by
    exact_mod_cast hCenter
  unfold physicalX
  apply sub_nonneg.mpr
  apply (le_div_iff₀ hmReal).2
  nlinarith

private theorem physicalX_nonpos_of_le_center {m : Nat} (hm : 0 < m)
    (sample : GridSample m) (hCenter : sample.x <= 2 * m) :
    physicalX sample <= 0 := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hCast : (sample.x : Real) <= (2 : Real) * (m : Real) := by
    exact_mod_cast hCenter
  unfold physicalX
  apply sub_nonpos.mpr
  apply (div_le_iff₀ hmReal).2
  nlinarith

private theorem physicalY_nonneg_of_center_le {m : Nat} (hm : 0 < m)
    (sample : GridSample m) (hCenter : 2 * m <= sample.y) :
    0 <= physicalY sample := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hCast : (2 : Real) * (m : Real) <= (sample.y : Real) := by
    exact_mod_cast hCenter
  unfold physicalY
  apply sub_nonneg.mpr
  apply (le_div_iff₀ hmReal).2
  nlinarith

private theorem physicalY_nonpos_of_le_center {m : Nat} (hm : 0 < m)
    (sample : GridSample m) (hCenter : sample.y <= 2 * m) :
    physicalY sample <= 0 := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hCast : (sample.y : Real) <= (2 : Real) * (m : Real) := by
    exact_mod_cast hCenter
  unfold physicalY
  apply sub_nonpos.mpr
  apply (div_le_iff₀ hmReal).2
  nlinarith

private theorem target_abs_radius {target : RealPlanePoint}
    (hTarget : onTargetCircle target) :
    |target.x| ^ 2 + |target.y| ^ 2 = 2 := by
  unfold onTargetCircle squaredRadius at hTarget
  simpa [sq_abs] using hTarget

private theorem edge_inside_radius {m : Nat} (hm : 0 < m)
    (edge : CrossingEdge m) :
    squaredRadius (physicalPoint (innerPoint edge)) <= 2 :=
  physicalPoint_inside hm (innerPoint edge) (innerPoint_inside edge)

private theorem edge_outside_radius {m : Nat} (hm : 0 < m)
    (edge : CrossingEdge m) :
    2 < squaredRadius (physicalPoint (outerPoint edge)) :=
  physicalPoint_outside hm (outerPoint edge) (outerPoint_outside edge)

theorem right_edge_coordinate_bounds {m : Nat} (hm : 0 < m)
    (target : RealPlanePoint) (hTarget : onTargetCircle target)
    (horizontal : FourAxisCrossings m (targetAxis m target))
    (edge : CrossingEdge m)
    (hInner : innerPoint edge = horizontal.right.insidePoint)
    (hOuter : outerPoint edge = horizontal.right.outsidePoint)
    (hDominant : |target.y| <= |target.x|)
    (hSign : 0 <= target.x) :
    |target.x - (edgePhysicalInterpolation edge).x| <= 3 / (m : Real) /\
      |target.y - (edgePhysicalInterpolation edge).y| <= 1 / (m : Real) := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hInnerAxis : (innerPoint edge).y = targetAxis m target := by
    calc
      (innerPoint edge).y = horizontal.right.insidePoint.y := congrArg GridSample.y hInner
      _ = targetAxis m target := horizontal.right_inside_axis
  have hOuterAxis : (outerPoint edge).y = targetAxis m target := by
    calc
      (outerPoint edge).y = horizontal.right.outsidePoint.y := congrArg GridSample.y hOuter
      _ = targetAxis m target := horizontal.right_outside_axis
  have hInnerY := physicalY_of_targetAxis hm target hTarget (innerPoint edge) hInnerAxis
  have hOuterY := physicalY_of_targetAxis hm target hTarget (outerPoint edge) hOuterAxis
  have hStep : (outerPoint edge).x = (innerPoint edge).x + 1 := by
    calc
      (outerPoint edge).x = horizontal.right.outsidePoint.x := congrArg GridSample.x hOuter
      _ = horizontal.right.insidePoint.x + 1 := horizontal.right_advances
      _ = (innerPoint edge).x + 1 := by rw [hInner]
  have hInnerCenter : 2 * m <= (innerPoint edge).x := by
    rw [hInner]
    exact horizontal.right_inside_center_le
  have hInRadius := edge_inside_radius hm edge
  have hOutRadius := edge_outside_radius hm edge
  have hInRadial :
      physicalX (innerPoint edge) ^ 2 +
          |inwardRoundedCoordinate m target.y| ^ 2 <= 2 := by
    simpa [squaredRadius, physicalPoint, hInnerY, sq_abs] using hInRadius
  have hOutRadial :
      2 < physicalX (outerPoint edge) ^ 2 +
          |inwardRoundedCoordinate m target.y| ^ 2 := by
    simpa [squaredRadius, physicalPoint, hOuterY, sq_abs] using hOutRadius
  have ht := edgePhysicalInterpolation_parameter_mem edge
  have hRadial := radial_bracket_affine_error
    (m : Real) |target.x| |target.y|
    |inwardRoundedCoordinate m target.y|
    (physicalX (innerPoint edge)) (physicalX (outerPoint edge))
    (realParameter (interpolationParameter edge))
    hmReal ((dominant_coordinate_ge_one hTarget).1 hDominant)
    (abs_nonneg target.y) (abs_nonneg _)
    (inwardRounded_abs_le m hm target.y)
    (inwardRounded_abs_gap_lt m hm target.y)
    (physicalX_nonneg_of_center_le hm (innerPoint edge) hInnerCenter)
    (physicalX_step_right hm (innerPoint edge) (outerPoint edge) hStep)
    hInRadial hOutRadial (target_abs_radius hTarget) ht.1 ht.2
  constructor
  · simpa [edgePhysicalInterpolation_x, abs_of_nonneg hSign] using hRadial
  · have hPointY :
        (edgePhysicalInterpolation edge).y =
          inwardRoundedCoordinate m target.y := by
      rw [edgePhysicalInterpolation_y, hInnerY, hOuterY]
      ring
    rw [hPointY]
    exact le_of_lt (inwardRoundedCoordinate_error hm target.y)

theorem left_edge_coordinate_bounds {m : Nat} (hm : 0 < m)
    (target : RealPlanePoint) (hTarget : onTargetCircle target)
    (horizontal : FourAxisCrossings m (targetAxis m target))
    (edge : CrossingEdge m)
    (hInner : innerPoint edge = horizontal.left.insidePoint)
    (hOuter : outerPoint edge = horizontal.left.outsidePoint)
    (hDominant : |target.y| <= |target.x|)
    (hSign : target.x < 0) :
    |target.x - (edgePhysicalInterpolation edge).x| <= 3 / (m : Real) /\
      |target.y - (edgePhysicalInterpolation edge).y| <= 1 / (m : Real) := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hInnerAxis : (innerPoint edge).y = targetAxis m target := by
    calc
      (innerPoint edge).y = horizontal.left.insidePoint.y := congrArg GridSample.y hInner
      _ = targetAxis m target := horizontal.left_inside_axis
  have hOuterAxis : (outerPoint edge).y = targetAxis m target := by
    calc
      (outerPoint edge).y = horizontal.left.outsidePoint.y := congrArg GridSample.y hOuter
      _ = targetAxis m target := horizontal.left_outside_axis
  have hInnerY := physicalY_of_targetAxis hm target hTarget (innerPoint edge) hInnerAxis
  have hOuterY := physicalY_of_targetAxis hm target hTarget (outerPoint edge) hOuterAxis
  have hStep : (outerPoint edge).x + 1 = (innerPoint edge).x := by
    calc
      (outerPoint edge).x + 1 = horizontal.left.outsidePoint.x + 1 := by rw [hOuter]
      _ = horizontal.left.insidePoint.x := horizontal.left_advances
      _ = (innerPoint edge).x := by rw [hInner]
  have hInnerCenter : (innerPoint edge).x <= 2 * m := by
    rw [hInner]
    exact horizontal.left_inside_le_center
  have hInnerNonpos := physicalX_nonpos_of_le_center hm (innerPoint edge) hInnerCenter
  have hPhysicalStep := physicalX_step_left hm (innerPoint edge) (outerPoint edge) hStep
  have hInRadius := edge_inside_radius hm edge
  have hOutRadius := edge_outside_radius hm edge
  have hInRadial :
      (-physicalX (innerPoint edge)) ^ 2 +
          |inwardRoundedCoordinate m target.y| ^ 2 <= 2 := by
    simpa [squaredRadius, physicalPoint, hInnerY, sq_abs] using hInRadius
  have hOutRadial :
      2 < (-physicalX (outerPoint edge)) ^ 2 +
          |inwardRoundedCoordinate m target.y| ^ 2 := by
    simpa [squaredRadius, physicalPoint, hOuterY, sq_abs] using hOutRadius
  have ht := edgePhysicalInterpolation_parameter_mem edge
  have hRadial := radial_bracket_affine_error
    (m : Real) |target.x| |target.y|
    |inwardRoundedCoordinate m target.y|
    (-physicalX (innerPoint edge)) (-physicalX (outerPoint edge))
    (realParameter (interpolationParameter edge))
    hmReal ((dominant_coordinate_ge_one hTarget).1 hDominant)
    (abs_nonneg target.y) (abs_nonneg _)
    (inwardRounded_abs_le m hm target.y)
    (inwardRounded_abs_gap_lt m hm target.y)
    (neg_nonneg.mpr hInnerNonpos)
    (by nlinarith) hInRadial hOutRadial (target_abs_radius hTarget) ht.1 ht.2
  constructor
  · have hRewrite :
        |(|target.x| -
            ((1 - realParameter (interpolationParameter edge)) *
                (-physicalX (innerPoint edge)) +
              realParameter (interpolationParameter edge) *
                (-physicalX (outerPoint edge))))| =
          |target.x - (edgePhysicalInterpolation edge).x| := by
      rw [abs_of_neg hSign, edgePhysicalInterpolation_x]
      rw [← abs_neg (target.x -
        ((1 - realParameter (interpolationParameter edge)) *
            physicalX (innerPoint edge) +
          realParameter (interpolationParameter edge) *
            physicalX (outerPoint edge)))]
      congr 1
      ring
    rw [hRewrite] at hRadial
    exact hRadial
  · have hPointY :
        (edgePhysicalInterpolation edge).y =
          inwardRoundedCoordinate m target.y := by
      rw [edgePhysicalInterpolation_y, hInnerY, hOuterY]
      ring
    rw [hPointY]
    exact le_of_lt (inwardRoundedCoordinate_error hm target.y)

theorem top_edge_coordinate_bounds {m : Nat} (hm : 0 < m)
    (target : RealPlanePoint) (hTarget : onTargetCircle target)
    (vertical : FourAxisCrossings m (targetAxis m (swapTarget target)))
    (edge : CrossingEdge m)
    (hInner : innerPoint edge = vertical.top.insidePoint)
    (hOuter : outerPoint edge = vertical.top.outsidePoint)
    (hDominant : ¬ |target.y| <= |target.x|)
    (hSign : 0 <= target.y) :
    |target.x - (edgePhysicalInterpolation edge).x| <= 1 / (m : Real) /\
      |target.y - (edgePhysicalInterpolation edge).y| <= 3 / (m : Real) := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hInnerAxis : (innerPoint edge).x = targetAxis m (swapTarget target) := by
    calc
      (innerPoint edge).x = vertical.top.insidePoint.x := congrArg GridSample.x hInner
      _ = targetAxis m (swapTarget target) := vertical.top_inside_axis
  have hOuterAxis : (outerPoint edge).x = targetAxis m (swapTarget target) := by
    calc
      (outerPoint edge).x = vertical.top.outsidePoint.x := congrArg GridSample.x hOuter
      _ = targetAxis m (swapTarget target) := vertical.top_outside_axis
  have hInnerX := physicalX_of_swappedTargetAxis hm target hTarget
    (innerPoint edge) hInnerAxis
  have hOuterX := physicalX_of_swappedTargetAxis hm target hTarget
    (outerPoint edge) hOuterAxis
  have hStep : (outerPoint edge).y = (innerPoint edge).y + 1 := by
    calc
      (outerPoint edge).y = vertical.top.outsidePoint.y := congrArg GridSample.y hOuter
      _ = vertical.top.insidePoint.y + 1 := vertical.top_advances
      _ = (innerPoint edge).y + 1 := by rw [hInner]
  have hInnerCenter : 2 * m <= (innerPoint edge).y := by
    rw [hInner]
    exact vertical.top_inside_center_le
  have hInRadius := edge_inside_radius hm edge
  have hOutRadius := edge_outside_radius hm edge
  have hInRadial :
      physicalY (innerPoint edge) ^ 2 +
          |inwardRoundedCoordinate m target.x| ^ 2 <= 2 := by
    simpa [squaredRadius, physicalPoint, hInnerX, sq_abs, add_comm] using hInRadius
  have hOutRadial :
      2 < physicalY (outerPoint edge) ^ 2 +
          |inwardRoundedCoordinate m target.x| ^ 2 := by
    simpa [squaredRadius, physicalPoint, hOuterX, sq_abs, add_comm] using hOutRadius
  have ht := edgePhysicalInterpolation_parameter_mem edge
  have hRadial := radial_bracket_affine_error
    (m : Real) |target.y| |target.x|
    |inwardRoundedCoordinate m target.x|
    (physicalY (innerPoint edge)) (physicalY (outerPoint edge))
    (realParameter (interpolationParameter edge))
    hmReal ((dominant_coordinate_ge_one hTarget).2 hDominant)
    (abs_nonneg target.x) (abs_nonneg _)
    (inwardRounded_abs_le m hm target.x)
    (inwardRounded_abs_gap_lt m hm target.x)
    (physicalY_nonneg_of_center_le hm (innerPoint edge) hInnerCenter)
    (physicalY_step_up hm (innerPoint edge) (outerPoint edge) hStep)
    hInRadial hOutRadial (by simpa [add_comm] using target_abs_radius hTarget)
    ht.1 ht.2
  constructor
  · have hPointX :
        (edgePhysicalInterpolation edge).x =
          inwardRoundedCoordinate m target.x := by
      rw [edgePhysicalInterpolation_x, hInnerX, hOuterX]
      ring
    rw [hPointX]
    exact le_of_lt (inwardRoundedCoordinate_error hm target.x)
  · simpa [edgePhysicalInterpolation_y, abs_of_nonneg hSign] using hRadial

theorem bottom_edge_coordinate_bounds {m : Nat} (hm : 0 < m)
    (target : RealPlanePoint) (hTarget : onTargetCircle target)
    (vertical : FourAxisCrossings m (targetAxis m (swapTarget target)))
    (edge : CrossingEdge m)
    (hInner : innerPoint edge = vertical.bottom.insidePoint)
    (hOuter : outerPoint edge = vertical.bottom.outsidePoint)
    (hDominant : ¬ |target.y| <= |target.x|)
    (hSign : target.y < 0) :
    |target.x - (edgePhysicalInterpolation edge).x| <= 1 / (m : Real) /\
      |target.y - (edgePhysicalInterpolation edge).y| <= 3 / (m : Real) := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hInnerAxis : (innerPoint edge).x = targetAxis m (swapTarget target) := by
    calc
      (innerPoint edge).x = vertical.bottom.insidePoint.x := congrArg GridSample.x hInner
      _ = targetAxis m (swapTarget target) := vertical.bottom_inside_axis
  have hOuterAxis : (outerPoint edge).x = targetAxis m (swapTarget target) := by
    calc
      (outerPoint edge).x = vertical.bottom.outsidePoint.x := congrArg GridSample.x hOuter
      _ = targetAxis m (swapTarget target) := vertical.bottom_outside_axis
  have hInnerX := physicalX_of_swappedTargetAxis hm target hTarget
    (innerPoint edge) hInnerAxis
  have hOuterX := physicalX_of_swappedTargetAxis hm target hTarget
    (outerPoint edge) hOuterAxis
  have hStep : (outerPoint edge).y + 1 = (innerPoint edge).y := by
    calc
      (outerPoint edge).y + 1 = vertical.bottom.outsidePoint.y + 1 := by rw [hOuter]
      _ = vertical.bottom.insidePoint.y := vertical.bottom_advances
      _ = (innerPoint edge).y := by rw [hInner]
  have hInnerCenter : (innerPoint edge).y <= 2 * m := by
    rw [hInner]
    exact vertical.bottom_inside_le_center
  have hInnerNonpos := physicalY_nonpos_of_le_center hm (innerPoint edge) hInnerCenter
  have hPhysicalStep := physicalY_step_down hm (innerPoint edge) (outerPoint edge) hStep
  have hInRadius := edge_inside_radius hm edge
  have hOutRadius := edge_outside_radius hm edge
  have hInRadial :
      (-physicalY (innerPoint edge)) ^ 2 +
          |inwardRoundedCoordinate m target.x| ^ 2 <= 2 := by
    simpa [squaredRadius, physicalPoint, hInnerX, sq_abs, add_comm] using hInRadius
  have hOutRadial :
      2 < (-physicalY (outerPoint edge)) ^ 2 +
          |inwardRoundedCoordinate m target.x| ^ 2 := by
    simpa [squaredRadius, physicalPoint, hOuterX, sq_abs, add_comm] using hOutRadius
  have ht := edgePhysicalInterpolation_parameter_mem edge
  have hRadial := radial_bracket_affine_error
    (m : Real) |target.y| |target.x|
    |inwardRoundedCoordinate m target.x|
    (-physicalY (innerPoint edge)) (-physicalY (outerPoint edge))
    (realParameter (interpolationParameter edge))
    hmReal ((dominant_coordinate_ge_one hTarget).2 hDominant)
    (abs_nonneg target.x) (abs_nonneg _)
    (inwardRounded_abs_le m hm target.x)
    (inwardRounded_abs_gap_lt m hm target.x)
    (neg_nonneg.mpr hInnerNonpos)
    (by nlinarith) hInRadial hOutRadial
    (by simpa [add_comm] using target_abs_radius hTarget) ht.1 ht.2
  constructor
  · have hPointX :
        (edgePhysicalInterpolation edge).x =
          inwardRoundedCoordinate m target.x := by
      rw [edgePhysicalInterpolation_x, hInnerX, hOuterX]
      ring
    rw [hPointX]
    exact le_of_lt (inwardRoundedCoordinate_error hm target.x)
  · have hRewrite :
        |(|target.y| -
            ((1 - realParameter (interpolationParameter edge)) *
                (-physicalY (innerPoint edge)) +
              realParameter (interpolationParameter edge) *
                (-physicalY (outerPoint edge))))| =
          |target.y - (edgePhysicalInterpolation edge).y| := by
      rw [abs_of_neg hSign, edgePhysicalInterpolation_y]
      rw [← abs_neg (target.y -
        ((1 - realParameter (interpolationParameter edge)) *
            physicalY (innerPoint edge) +
          realParameter (interpolationParameter edge) *
            physicalY (outerPoint edge)))]
      congr 1
      ring
    rw [hRewrite] at hRadial
    exact hRadial

theorem euclideanDistance_le_four_div {m : Nat} (hm : 0 < m)
    (target point : RealPlanePoint)
    (hx : |target.x - point.x| <= 3 / (m : Real))
    (hy : |target.y - point.y| <= 1 / (m : Real)) :
    euclideanDistance target point <= 4 / (m : Real) := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hThree : 0 <= 3 / (m : Real) := by positivity
  have hOne : 0 <= 1 / (m : Real) := by positivity
  have hxSquare := (sq_le_sq₀ (abs_nonneg (target.x - point.x)) hThree).2 hx
  have hySquare := (sq_le_sq₀ (abs_nonneg (target.y - point.y)) hOne).2 hy
  rw [sq_abs] at hxSquare hySquare
  have hSquared : squaredDistance target point <= (4 / (m : Real)) ^ 2 := by
    unfold squaredDistance
    have hInvSquare : 0 <= (1 / (m : Real)) ^ 2 := sq_nonneg _
    have hxSquare' :
        (target.x - point.x) ^ 2 <= 9 * (1 / (m : Real)) ^ 2 := by
      calc
        (target.x - point.x) ^ 2 <= (3 / (m : Real)) ^ 2 := hxSquare
        _ = 9 * (1 / (m : Real)) ^ 2 := by ring
    have hySquare' :
        (target.y - point.y) ^ 2 <= (1 / (m : Real)) ^ 2 := hySquare
    calc
      (target.x - point.x) ^ 2 + (target.y - point.y) ^ 2 <=
          10 * (1 / (m : Real)) ^ 2 := by nlinarith
      _ <= 16 * (1 / (m : Real)) ^ 2 := by nlinarith
      _ = (4 / (m : Real)) ^ 2 := by ring
  have hSquaredNonneg : 0 <= squaredDistance target point := by
    unfold squaredDistance
    positivity
  have hRootSquare := Real.sq_sqrt hSquaredNonneg
  have hRootNonneg := Real.sqrt_nonneg (squaredDistance target point)
  have hBoundNonneg : 0 <= 4 / (m : Real) := by positivity
  unfold euclideanDistance
  nlinarith

theorem euclideanDistance_le_four_div_swapped {m : Nat} (hm : 0 < m)
    (target point : RealPlanePoint)
    (hx : |target.x - point.x| <= 1 / (m : Real))
    (hy : |target.y - point.y| <= 3 / (m : Real)) :
    euclideanDistance target point <= 4 / (m : Real) := by
  have h := euclideanDistance_le_four_div hm
    (swapTarget target) (swapTarget point) hy hx
  simpa [euclideanDistance, squaredDistance, swapTarget, add_comm] using h

end
end DominantBranchCoordinateBound
end BoundaryOfSelf

#print axioms BoundaryOfSelf.DominantBranchCoordinateBound.right_edge_coordinate_bounds
#print axioms BoundaryOfSelf.DominantBranchCoordinateBound.left_edge_coordinate_bounds
#print axioms BoundaryOfSelf.DominantBranchCoordinateBound.top_edge_coordinate_bounds
#print axioms BoundaryOfSelf.DominantBranchCoordinateBound.bottom_edge_coordinate_bounds
#print axioms BoundaryOfSelf.DominantBranchCoordinateBound.euclideanDistance_le_four_div
#print axioms BoundaryOfSelf.DominantBranchCoordinateBound.euclideanDistance_le_four_div_swapped
