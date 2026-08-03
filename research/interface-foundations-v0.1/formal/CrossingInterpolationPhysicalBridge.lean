import GridPhysicalCoordinateAdapter

namespace BoundaryOfSelf
namespace CrossingInterpolationPhysicalBridge

noncomputable section

open InterpolatedBoundaryContour
open InterpolatedSignedCoordinates
open LocalPolygonalContour
open LocalSegmentRadialBound
open LocalSegmentRealCompletion
open OneSidedEuclideanContourBound
open GridPhysicalCoordinateAdapter

/-!
IF-BS-22F-B3C2B2B identifies the exact IF-BS-10 threshold interpolation in
two representations: an affine interpolation of normalized grid samples and
the common-denominator endpoint used by every IF-BS-22C/D real segment.
-/

def edgePhysicalInterpolation {m : Nat} (edge : CrossingEdge m) :
    RealPlanePoint :=
  realSegmentPoint (realParameter (interpolationParameter edge))
    (physicalPoint (innerPoint edge)) (physicalPoint (outerPoint edge))

@[simp] theorem edgePhysicalInterpolation_x {m : Nat} (edge : CrossingEdge m) :
    (edgePhysicalInterpolation edge).x =
      (1 - realParameter (interpolationParameter edge)) *
          physicalX (innerPoint edge) +
        realParameter (interpolationParameter edge) *
          physicalX (outerPoint edge) := rfl

@[simp] theorem edgePhysicalInterpolation_y {m : Nat} (edge : CrossingEdge m) :
    (edgePhysicalInterpolation edge).y =
      (1 - realParameter (interpolationParameter edge)) *
          physicalY (innerPoint edge) +
        realParameter (interpolationParameter edge) *
          physicalY (outerPoint edge) := rfl

theorem firstRealEndpoint_self_eq_physical {m : Nat} (hm : 0 < m)
    (edge : CrossingEdge m) :
    firstRealEndpoint edge edge = edgePhysicalInterpolation edge := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hd : 0 < interpolationDenominator edge :=
    interpolationDenominator_pos edge
  have hdReal : (0 : Real) < interpolationDenominator edge := by
    exact_mod_cast hd
  apply RealPlanePoint.ext
  · rw [edgePhysicalInterpolation_x]
    rw [physicalX_eq_centered hm, physicalX_eq_centered hm]
    unfold firstRealEndpoint realCommonDenominator commonCenteredXFirst
      commonDenominator commonScale realParameter interpolationParameter
      interpolatedXNumerator innerWeight outerWeight
    dsimp
    push_cast
    field_simp [ne_of_gt hmReal, ne_of_gt hdReal]
  · rw [edgePhysicalInterpolation_y]
    rw [physicalY_eq_centered hm, physicalY_eq_centered hm]
    unfold firstRealEndpoint realCommonDenominator commonCenteredYFirst
      commonDenominator commonScale realParameter interpolationParameter
      interpolatedYNumerator innerWeight outerWeight
    dsimp
    push_cast
    field_simp [ne_of_gt hmReal, ne_of_gt hdReal]

theorem segmentRealPoint_zero_self_eq_physical {m : Nat} (hm : 0 < m)
    (segment : LocalContourSegment m) (vertex : SegmentVertex segment) :
    segmentRealPoint 0 segment vertex vertex =
      edgePhysicalInterpolation (segmentEdge segment vertex) := by
  unfold segmentRealPoint realSegmentPoint
  dsimp
  rw [firstRealEndpoint_self_eq_physical hm]
  apply RealPlanePoint.ext <;> simp

theorem edgePhysicalInterpolation_parameter_mem {m : Nat}
    (edge : CrossingEdge m) :
    0 <= realParameter (interpolationParameter edge) /\
      realParameter (interpolationParameter edge) <= 1 :=
  realParameter_mem_unitInterval (interpolationParameter edge)

end
end CrossingInterpolationPhysicalBridge
end BoundaryOfSelf

#print axioms BoundaryOfSelf.CrossingInterpolationPhysicalBridge.firstRealEndpoint_self_eq_physical
#print axioms BoundaryOfSelf.CrossingInterpolationPhysicalBridge.segmentRealPoint_zero_self_eq_physical
#print axioms BoundaryOfSelf.CrossingInterpolationPhysicalBridge.edgePhysicalInterpolation_parameter_mem
