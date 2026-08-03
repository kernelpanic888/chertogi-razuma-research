import GlobalContourIncidence

namespace BoundaryOfSelf
namespace GlobalContourIncidenceAudit

open UniformRadialBoundaryFamily
open LocalPolygonalContour
open GlobalContourIncidence

example {m : Nat} (hm : 0 < m) :
    thresholdNumerator m < (2 * m) * (2 * m) := by
  exact threshold_lt_outer_square hm

example {m : Nat} (hm : 0 < m) (e : HorizontalGridEdge m)
    (h : HorizontalCrosses e) : 0 < e.y /\ e.y < 4 * m := by
  exact horizontal_crossing_is_interior hm e h

example {m : Nat} (hm : 0 < m) (e : VerticalGridEdge m)
    (h : VerticalCrosses e) : 0 < e.x /\ e.x < 4 * m := by
  exact vertical_crossing_is_interior hm e h

example {m : Nat} (hm : 0 < m) (e : HorizontalGridEdge m)
    (h : HorizontalCrosses e) :
    exists below above : LocalContourSegment m,
      CellSide.north ∈ segmentSides below /\
      CellSide.south ∈ segmentSides above := by
  exact horizontal_crossing_has_two_incident_segments hm e h

example {m : Nat} (hm : 0 < m) (e : VerticalGridEdge m)
    (h : VerticalCrosses e) :
    exists left right : LocalContourSegment m,
      CellSide.east ∈ segmentSides left /\
      CellSide.west ∈ segmentSides right := by
  exact vertical_crossing_has_two_incident_segments hm e h

#print axioms threshold_lt_outer_square
#print axioms horizontal_crossing_is_interior
#print axioms vertical_crossing_is_interior
#print axioms horizontal_crossing_has_two_incident_segments
#print axioms vertical_crossing_has_two_incident_segments

end GlobalContourIncidenceAudit
end BoundaryOfSelf
