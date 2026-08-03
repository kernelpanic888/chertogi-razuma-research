import InterpolatedBoundaryContour

namespace BoundaryOfSelf
namespace LocalPolygonalContour

open UniformRadialBoundaryFamily
open InterpolatedBoundaryContour

/-!
IF-BS-11 is the local marching-squares assembly theorem for the radial field.
Every active cell has exactly two crossing sides, because cyclic crossings are
even and the radial parallelogram identity excludes the alternating four-side
case. The two exact IF-BS-10 edge points therefore determine one local segment.
-/

structure GridCell (m : Nat) where
  x : Nat
  y : Nat
  x_lt : x < 4 * m
  y_lt : y < 4 * m

def southWest {m : Nat} (c : GridCell m) : GridSample m where
  x := c.x
  y := c.y
  x_le := by have h := c.x_lt; omega
  y_le := by have h := c.y_lt; omega

def southEast {m : Nat} (c : GridCell m) : GridSample m where
  x := c.x + 1
  y := c.y
  x_le := by have h := c.x_lt; omega
  y_le := by have h := c.y_lt; omega

def northEast {m : Nat} (c : GridCell m) : GridSample m where
  x := c.x + 1
  y := c.y + 1
  x_le := by have h := c.x_lt; omega
  y_le := by have h := c.y_lt; omega

def northWest {m : Nat} (c : GridCell m) : GridSample m where
  x := c.x
  y := c.y + 1
  x_le := by have h := c.x_lt; omega
  y_le := by have h := c.y_lt; omega

inductive CellSide where
  | south
  | east
  | north
  | west
deriving DecidableEq, Repr

def sideStart {m : Nat} (c : GridCell m) : CellSide -> GridSample m
  | .south => southWest c
  | .east => southEast c
  | .north => northEast c
  | .west => northWest c

def sideEnd {m : Nat} (c : GridCell m) : CellSide -> GridSample m
  | .south => southEast c
  | .east => northEast c
  | .north => northWest c
  | .west => southWest c

theorem side_adjacent {m : Nat} (c : GridCell m) (s : CellSide) :
    UnitAdjacent (sideStart c s) (sideEnd c s) := by
  cases s <;>
    simp [sideStart, sideEnd, southWest, southEast, northEast, northWest,
      UnitAdjacent]

def insideFlag {m : Nat} (p : GridSample m) : Bool :=
  decide (radialNumerator p <= thresholdNumerator m)

def sideCrossingFlag {m : Nat} (c : GridCell m) (s : CellSide) : Bool :=
  insideFlag (sideStart c s) != insideFlag (sideEnd c s)

theorem sideCrossingFlag_eq_true_iff {m : Nat} (c : GridCell m)
    (s : CellSide) :
    sideCrossingFlag c s = true <->
      Crosses (sideStart c s) (sideEnd c s) := by
  by_cases hp : radialNumerator (sideStart c s) <= thresholdNumerator m <;>
  by_cases hq : radialNumerator (sideEnd c s) <= thresholdNumerator m <;>
  simp [sideCrossingFlag, insideFlag, Crosses, Inside, hp, hq]

def allSides : List CellSide :=
  [.south, .east, .north, .west]

def crossingSides {m : Nat} (c : GridCell m) : List CellSide :=
  allSides.filter (fun s => sideCrossingFlag c s)

theorem mem_crossingSides_iff {m : Nat} (c : GridCell m)
    (s : CellSide) :
    s ∈ crossingSides c <-> sideCrossingFlag c s = true := by
  cases s <;> simp [crossingSides, allSides]

theorem cell_parallelogram {m : Nat} (c : GridCell m) :
    radialNumerator (southWest c) + radialNumerator (northEast c) =
    radialNumerator (southEast c) + radialNumerator (northWest c) := by
  unfold radialNumerator
  simp [xOffset, yOffset, southWest, southEast, northEast, northWest]
  omega

theorem crossingSides_length_cases {m : Nat} (c : GridCell m) :
    (crossingSides c).length = 0 \/
    (crossingSides c).length = 2 \/
    (crossingSides c).length = 4 := by
  by_cases hsw : radialNumerator (southWest c) <= thresholdNumerator m <;>
  by_cases hse : radialNumerator (southEast c) <= thresholdNumerator m <;>
  by_cases hne : radialNumerator (northEast c) <= thresholdNumerator m <;>
  by_cases hnw : radialNumerator (northWest c) <= thresholdNumerator m <;>
  simp [crossingSides, allSides, sideCrossingFlag, insideFlag, sideStart,
    sideEnd, hsw, hse, hne, hnw]

theorem crossingSides_length_ne_four {m : Nat} (c : GridCell m) :
    (crossingSides c).length ≠ 4 := by
  intro hFour
  have hParallelogram := cell_parallelogram c
  by_cases hsw : radialNumerator (southWest c) <= thresholdNumerator m <;>
  by_cases hse : radialNumerator (southEast c) <= thresholdNumerator m <;>
  by_cases hne : radialNumerator (northEast c) <= thresholdNumerator m <;>
  by_cases hnw : radialNumerator (northWest c) <= thresholdNumerator m <;>
  simp [crossingSides, allSides, sideCrossingFlag, insideFlag, sideStart,
    sideEnd, hsw, hse, hne, hnw] at hFour <;>
  omega

def ActiveCell {m : Nat} (c : GridCell m) : Prop :=
  0 < (crossingSides c).length

theorem activeCell_has_exactly_two_sides {m : Nat} (c : GridCell m)
    (hActive : ActiveCell c) :
    (crossingSides c).length = 2 := by
  rcases crossingSides_length_cases c with hZero | hTwo | hFour
  · unfold ActiveCell at hActive
    omega
  · exact hTwo
  · exact False.elim (crossingSides_length_ne_four c hFour)

def crossingEdgeForSide {m : Nat} (c : GridCell m) (s : CellSide)
    (h : s ∈ crossingSides c) : CrossingEdge m where
  p := sideStart c s
  q := sideEnd c s
  adjacent := side_adjacent c s
  crosses := (sideCrossingFlag_eq_true_iff c s).mp
    ((mem_crossingSides_iff c s).mp h)

structure LocalContourSegment (m : Nat) where
  cell : GridCell m
  active : ActiveCell cell

def segmentSides {m : Nat} (segment : LocalContourSegment m) : List CellSide :=
  crossingSides segment.cell

theorem segment_has_exactly_two_vertices {m : Nat}
    (segment : LocalContourSegment m) :
    (segmentSides segment).length = 2 := by
  exact activeCell_has_exactly_two_sides segment.cell segment.active

def SegmentVertex {m : Nat} (segment : LocalContourSegment m) :=
  {s : CellSide // s ∈ segmentSides segment}

def segmentVertexPoint {m : Nat} (segment : LocalContourSegment m)
    (vertex : SegmentVertex segment) : UnitIntervalFraction :=
  interpolationParameter
    (crossingEdgeForSide segment.cell vertex.val vertex.property)

theorem crosses_comm {m : Nat} {p q : GridSample m}
    (h : Crosses p q) : Crosses q p := by
  rcases h with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact Or.inr ⟨hq, hp⟩
  · exact Or.inl ⟨hq, hp⟩

def reverseEdge {m : Nat} (e : CrossingEdge m) : CrossingEdge m where
  p := e.q
  q := e.p
  adjacent := unitAdjacent_comm e.adjacent
  crosses := crosses_comm e.crosses

theorem reverse_innerPoint {m : Nat} (e : CrossingEdge m) :
    innerPoint (reverseEdge e) = innerPoint e := by
  rcases e.crosses with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · unfold Inside at hp hq
    simp [reverseEdge, innerPoint, hp, hq]
  · unfold Inside at hp hq
    simp [reverseEdge, innerPoint, hp, hq]

theorem reverse_outerPoint {m : Nat} (e : CrossingEdge m) :
    outerPoint (reverseEdge e) = outerPoint e := by
  rcases e.crosses with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · unfold Inside at hp hq
    simp [reverseEdge, outerPoint, hp, hq]
  · unfold Inside at hp hq
    simp [reverseEdge, outerPoint, hp, hq]

theorem reverse_interpolationNumerator {m : Nat} (e : CrossingEdge m) :
    interpolationNumerator (reverseEdge e) = interpolationNumerator e := by
  unfold interpolationNumerator
  rw [reverse_innerPoint]

theorem reverse_interpolationDenominator {m : Nat} (e : CrossingEdge m) :
    interpolationDenominator (reverseEdge e) = interpolationDenominator e := by
  unfold interpolationDenominator
  rw [reverse_innerPoint, reverse_outerPoint]

theorem reverse_parameter_coordinates {m : Nat} (e : CrossingEdge m) :
    (interpolationParameter (reverseEdge e)).numerator =
      (interpolationParameter e).numerator /\
    (interpolationParameter (reverseEdge e)).denominator =
      (interpolationParameter e).denominator := by
  exact ⟨reverse_interpolationNumerator e, reverse_interpolationDenominator e⟩

end LocalPolygonalContour
end BoundaryOfSelf
