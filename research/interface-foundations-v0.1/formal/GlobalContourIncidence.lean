import LocalPolygonalContour

namespace BoundaryOfSelf
namespace GlobalContourIncidence

open UniformRadialBoundaryFamily
open InterpolatedBoundaryContour
open LocalPolygonalContour
open RefinedCurvedBoundaryGrid

/-!
IF-BS-12 proves that every radial crossing edge is strictly interior to the
finite grid and constructs the active local contour segment on each of its two
sides. This is the existence half of global degree-two incidence.
-/

structure HorizontalGridEdge (m : Nat) where
  x : Nat
  y : Nat
  x_lt : x < 4 * m
  y_le : y <= 4 * m

structure VerticalGridEdge (m : Nat) where
  x : Nat
  y : Nat
  x_le : x <= 4 * m
  y_lt : y < 4 * m

def horizontalStart {m : Nat} (e : HorizontalGridEdge m) : GridSample m where
  x := e.x
  y := e.y
  x_le := by have h := e.x_lt; omega
  y_le := e.y_le

def horizontalEnd {m : Nat} (e : HorizontalGridEdge m) : GridSample m where
  x := e.x + 1
  y := e.y
  x_le := by have h := e.x_lt; omega
  y_le := e.y_le

def verticalStart {m : Nat} (e : VerticalGridEdge m) : GridSample m where
  x := e.x
  y := e.y
  x_le := e.x_le
  y_le := by have h := e.y_lt; omega

def verticalEnd {m : Nat} (e : VerticalGridEdge m) : GridSample m where
  x := e.x
  y := e.y + 1
  x_le := e.x_le
  y_le := by have h := e.y_lt; omega

def HorizontalCrosses {m : Nat} (e : HorizontalGridEdge m) : Prop :=
  Crosses (horizontalStart e) (horizontalEnd e)

def VerticalCrosses {m : Nat} (e : VerticalGridEdge m) : Prop :=
  Crosses (verticalStart e) (verticalEnd e)

def HorizontalOuterBoundary {m : Nat} (e : HorizontalGridEdge m) : Prop :=
  e.y = 0 \/ e.y = 4 * m

def VerticalOuterBoundary {m : Nat} (e : VerticalGridEdge m) : Prop :=
  e.x = 0 \/ e.x = 4 * m

theorem zero_offset (m : Nat) :
    natDistance 0 (centerCoordinate m) = 2 * m := by
  simp [natDistance, centerCoordinate]

theorem four_mul_offset {m : Nat} (hm : 0 < m) :
    natDistance (4 * m) (centerCoordinate m) = 2 * m := by
  unfold natDistance centerCoordinate
  split <;> omega

theorem threshold_lt_outer_square {m : Nat} (hm : 0 < m) :
    thresholdNumerator m < (2 * m) * (2 * m) := by
  have hmm : 0 < m * m := Nat.mul_pos hm hm
  have hScaled : 2 * (m * m) < 4 * (m * m) := by omega
  simpa [thresholdNumerator, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using hScaled

theorem outside_of_x_outer {m : Nat} (hm : 0 < m)
    (p : GridSample m) (hOuter : p.x = 0 \/ p.x = 4 * m) :
    ¬ Inside p := by
  have hOffset : xOffset p = 2 * m := by
    rcases hOuter with hx | hx
    · simpa [xOffset, hx] using zero_offset m
    · simpa [xOffset, hx] using four_mul_offset hm
  have hStrict := threshold_lt_outer_square hm
  unfold Inside radialNumerator
  rw [hOffset]
  omega

theorem outside_of_y_outer {m : Nat} (hm : 0 < m)
    (p : GridSample m) (hOuter : p.y = 0 \/ p.y = 4 * m) :
    ¬ Inside p := by
  have hOffset : yOffset p = 2 * m := by
    rcases hOuter with hy | hy
    · simpa [yOffset, hy] using zero_offset m
    · simpa [yOffset, hy] using four_mul_offset hm
  have hStrict := threshold_lt_outer_square hm
  unfold Inside radialNumerator
  rw [hOffset]
  omega

theorem not_crosses_of_both_outside {m : Nat} {p q : GridSample m}
    (hp : ¬ Inside p) (hq : ¬ Inside q) : ¬ Crosses p q := by
  intro hCrosses
  rcases hCrosses with ⟨hip, hoq⟩ | ⟨hop, hiq⟩
  · exact hp hip
  · exact hq hiq

theorem horizontal_outer_boundary_not_crossing {m : Nat} (hm : 0 < m)
    (e : HorizontalGridEdge m) (hOuter : HorizontalOuterBoundary e) :
    ¬ HorizontalCrosses e := by
  apply not_crosses_of_both_outside
  · apply outside_of_y_outer hm
    simpa [HorizontalOuterBoundary, horizontalStart] using hOuter
  · apply outside_of_y_outer hm
    simpa [HorizontalOuterBoundary, horizontalEnd] using hOuter

theorem vertical_outer_boundary_not_crossing {m : Nat} (hm : 0 < m)
    (e : VerticalGridEdge m) (hOuter : VerticalOuterBoundary e) :
    ¬ VerticalCrosses e := by
  apply not_crosses_of_both_outside
  · apply outside_of_x_outer hm
    simpa [VerticalOuterBoundary, verticalStart] using hOuter
  · apply outside_of_x_outer hm
    simpa [VerticalOuterBoundary, verticalEnd] using hOuter

theorem horizontal_crossing_is_interior {m : Nat} (hm : 0 < m)
    (e : HorizontalGridEdge m) (hCrosses : HorizontalCrosses e) :
    0 < e.y /\ e.y < 4 * m := by
  have hNotOuter : ¬ HorizontalOuterBoundary e := by
    intro hOuter
    exact horizontal_outer_boundary_not_crossing hm e hOuter hCrosses
  unfold HorizontalOuterBoundary at hNotOuter
  have hy := e.y_le
  omega

theorem vertical_crossing_is_interior {m : Nat} (hm : 0 < m)
    (e : VerticalGridEdge m) (hCrosses : VerticalCrosses e) :
    0 < e.x /\ e.x < 4 * m := by
  have hNotOuter : ¬ VerticalOuterBoundary e := by
    intro hOuter
    exact vertical_outer_boundary_not_crossing hm e hOuter hCrosses
  unfold VerticalOuterBoundary at hNotOuter
  have hx := e.x_le
  omega

def horizontalBelowCell {m : Nat} (e : HorizontalGridEdge m)
    (hy : 0 < e.y) : GridCell m where
  x := e.x
  y := e.y - 1
  x_lt := e.x_lt
  y_lt := by have h := e.y_le; omega

def horizontalAboveCell {m : Nat} (e : HorizontalGridEdge m)
    (hy : e.y < 4 * m) : GridCell m where
  x := e.x
  y := e.y
  x_lt := e.x_lt
  y_lt := hy

def verticalLeftCell {m : Nat} (e : VerticalGridEdge m)
    (hx : 0 < e.x) : GridCell m where
  x := e.x - 1
  y := e.y
  x_lt := by have h := e.x_le; omega
  y_lt := e.y_lt

def verticalRightCell {m : Nat} (e : VerticalGridEdge m)
    (hx : e.x < 4 * m) : GridCell m where
  x := e.x
  y := e.y
  x_lt := hx
  y_lt := e.y_lt

theorem horizontal_below_north_mem {m : Nat} (e : HorizontalGridEdge m)
    (hy : 0 < e.y) (hCrosses : HorizontalCrosses e) :
    CellSide.north ∈ crossingSides (horizontalBelowCell e hy) := by
  apply (mem_crossingSides_iff _ _).mpr
  apply (sideCrossingFlag_eq_true_iff _ _).mpr
  have hReverse := crosses_comm hCrosses
  have hyOne : 1 <= e.y := by omega
  have hyCancel : e.y - 1 + 1 = e.y :=
    Nat.sub_add_cancel hyOne
  simpa [HorizontalCrosses, horizontalBelowCell, sideStart, sideEnd,
    northEast, northWest, horizontalStart, horizontalEnd,
    hyCancel] using hReverse

theorem horizontal_above_south_mem {m : Nat} (e : HorizontalGridEdge m)
    (hy : e.y < 4 * m) (hCrosses : HorizontalCrosses e) :
    CellSide.south ∈ crossingSides (horizontalAboveCell e hy) := by
  apply (mem_crossingSides_iff _ _).mpr
  apply (sideCrossingFlag_eq_true_iff _ _).mpr
  simpa [HorizontalCrosses, horizontalAboveCell, sideStart, sideEnd,
    southWest, southEast, horizontalStart, horizontalEnd] using hCrosses

theorem vertical_left_east_mem {m : Nat} (e : VerticalGridEdge m)
    (hx : 0 < e.x) (hCrosses : VerticalCrosses e) :
    CellSide.east ∈ crossingSides (verticalLeftCell e hx) := by
  apply (mem_crossingSides_iff _ _).mpr
  apply (sideCrossingFlag_eq_true_iff _ _).mpr
  have hxOne : 1 <= e.x := by omega
  have hxCancel : e.x - 1 + 1 = e.x :=
    Nat.sub_add_cancel hxOne
  simpa [VerticalCrosses, verticalLeftCell, sideStart, sideEnd,
    southEast, northEast, verticalStart, verticalEnd,
    hxCancel] using hCrosses

theorem vertical_right_west_mem {m : Nat} (e : VerticalGridEdge m)
    (hx : e.x < 4 * m) (hCrosses : VerticalCrosses e) :
    CellSide.west ∈ crossingSides (verticalRightCell e hx) := by
  apply (mem_crossingSides_iff _ _).mpr
  apply (sideCrossingFlag_eq_true_iff _ _).mpr
  have hReverse := crosses_comm hCrosses
  simpa [VerticalCrosses, verticalRightCell, sideStart, sideEnd,
    northWest, southWest, verticalStart, verticalEnd] using hReverse

theorem active_of_crossingSide_mem {m : Nat} {c : GridCell m}
    {s : CellSide} (h : s ∈ crossingSides c) : ActiveCell c := by
  unfold ActiveCell
  exact List.length_pos_of_mem h

theorem horizontal_crossing_has_two_incident_segments {m : Nat}
    (hm : 0 < m) (e : HorizontalGridEdge m)
    (hCrosses : HorizontalCrosses e) :
    exists below above : LocalContourSegment m,
      CellSide.north ∈ segmentSides below /\
      CellSide.south ∈ segmentSides above := by
  have hInterior := horizontal_crossing_is_interior hm e hCrosses
  have hBelow := horizontal_below_north_mem e hInterior.1 hCrosses
  have hAbove := horizontal_above_south_mem e hInterior.2 hCrosses
  let below : LocalContourSegment m :=
    ⟨horizontalBelowCell e hInterior.1, active_of_crossingSide_mem hBelow⟩
  let above : LocalContourSegment m :=
    ⟨horizontalAboveCell e hInterior.2, active_of_crossingSide_mem hAbove⟩
  exact ⟨below, above, hBelow, hAbove⟩

theorem vertical_crossing_has_two_incident_segments {m : Nat}
    (hm : 0 < m) (e : VerticalGridEdge m)
    (hCrosses : VerticalCrosses e) :
    exists left right : LocalContourSegment m,
      CellSide.east ∈ segmentSides left /\
      CellSide.west ∈ segmentSides right := by
  have hInterior := vertical_crossing_is_interior hm e hCrosses
  have hLeft := vertical_left_east_mem e hInterior.1 hCrosses
  have hRight := vertical_right_west_mem e hInterior.2 hCrosses
  let left : LocalContourSegment m :=
    ⟨verticalLeftCell e hInterior.1, active_of_crossingSide_mem hLeft⟩
  let right : LocalContourSegment m :=
    ⟨verticalRightCell e hInterior.2, active_of_crossingSide_mem hRight⟩
  exact ⟨left, right, hLeft, hRight⟩

end GlobalContourIncidence
end BoundaryOfSelf
