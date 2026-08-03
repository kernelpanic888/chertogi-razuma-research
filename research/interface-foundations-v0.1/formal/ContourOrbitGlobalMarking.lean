import ContourOrbitLocalParity

namespace BoundaryOfSelf
namespace ContourOrbitGlobalMarking

open UniformRadialBoundaryFamily
open LocalPolygonalContour
open GlobalContourIncidence
open GlobalContourZeroBoundary
open ConcreteRadialContourTraversal
open MinimalSeparatingContourOrbit
open RectangularParityPotential
open ContourOrbitLocalParity

/-!
IF-BS-20D packages the local side marks of IF-BS-20C as one global
horizontal/vertical coordinate marking. Coordinate uniqueness removes proof
dependence. The four global edge values around each cell coincide with its four
local side values, so local xor-zero becomes `ClosedOn` and IF-BS-20B yields a
global Boolean vertex potential.
-/

def HorizontalEdgeMarked {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (edge : HorizontalGridEdge m) : Prop :=
  exists state, SameContourOrbit hm anchor state /\
    RepresentsHorizontal state.val.1 state.val.2 edge

def VerticalEdgeMarked {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (edge : VerticalGridEdge m) : Prop :=
  exists state, SameContourOrbit hm anchor state /\
    RepresentsVertical state.val.1 state.val.2 edge

theorem horizontalEdgeMarked_iff_sideMarked {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (cell : GridCell m) (side : CellSide)
    (edge : HorizontalGridEdge m)
    (represents : RepresentsHorizontal cell side edge) :
    HorizontalEdgeMarked hm anchor edge <->
      SideMarkedByOrbit hm anchor cell side := by
  constructor
  · rintro ⟨state, state_orbit, state_represents⟩
    have current_same_state : SameUndirectedEdge
        (sideStart cell side) (sideEnd cell side)
        (sideStart state.val.1 state.val.2)
        (sideEnd state.val.1 state.val.2) :=
      sameUndirectedEdge_trans represents
        (sameUndirectedEdge_symm state_represents)
    have current_crosses : Crosses (sideStart cell side) (sideEnd cell side) :=
      crosses_of_sameUndirectedEdge current_same_state
        (contourState_side_crosses state)
    have side_crosses : side ∈ crossingSides cell :=
      (mem_crossingSides_iff cell side).mpr
        ((sideCrossingFlag_eq_true_iff cell side).mpr current_crosses)
    refine ⟨side_crosses, state, state_orbit, ?_⟩
    exact sameUndirectedEdge_trans state_represents
      (sameUndirectedEdge_symm represents)
  · rintro ⟨side_crosses, state, state_orbit, shares⟩
    exact ⟨state, state_orbit,
      sameUndirectedEdge_trans shares represents⟩

theorem verticalEdgeMarked_iff_sideMarked {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (cell : GridCell m) (side : CellSide)
    (edge : VerticalGridEdge m)
    (represents : RepresentsVertical cell side edge) :
    VerticalEdgeMarked hm anchor edge <->
      SideMarkedByOrbit hm anchor cell side := by
  constructor
  · rintro ⟨state, state_orbit, state_represents⟩
    have current_same_state : SameUndirectedEdge
        (sideStart cell side) (sideEnd cell side)
        (sideStart state.val.1 state.val.2)
        (sideEnd state.val.1 state.val.2) :=
      sameUndirectedEdge_trans represents
        (sameUndirectedEdge_symm state_represents)
    have current_crosses : Crosses (sideStart cell side) (sideEnd cell side) :=
      crosses_of_sameUndirectedEdge current_same_state
        (contourState_side_crosses state)
    have side_crosses : side ∈ crossingSides cell :=
      (mem_crossingSides_iff cell side).mpr
        ((sideCrossingFlag_eq_true_iff cell side).mpr current_crosses)
    refine ⟨side_crosses, state, state_orbit, ?_⟩
    exact sameUndirectedEdge_trans state_represents
      (sameUndirectedEdge_symm represents)
  · rintro ⟨side_crosses, state, state_orbit, shares⟩
    exact ⟨state, state_orbit,
      sameUndirectedEdge_trans shares represents⟩

theorem horizontalGridEdge_eq_of_coordinates {m : Nat}
    {left right : HorizontalGridEdge m}
    (x_eq : left.x = right.x) (y_eq : left.y = right.y) : left = right := by
  cases left
  cases right
  simp_all

theorem verticalGridEdge_eq_of_coordinates {m : Nat}
    {left right : VerticalGridEdge m}
    (x_eq : left.x = right.x) (y_eq : left.y = right.y) : left = right := by
  cases left
  cases right
  simp_all

def HorizontalCoordinateMarked {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (x y : Nat) : Prop :=
  exists edge : HorizontalGridEdge m,
    edge.x = x /\ edge.y = y /\ HorizontalEdgeMarked hm anchor edge

def VerticalCoordinateMarked {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (x y : Nat) : Prop :=
  exists edge : VerticalGridEdge m,
    edge.x = x /\ edge.y = y /\ VerticalEdgeMarked hm anchor edge

theorem horizontalCoordinateMarked_iff {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (edge : HorizontalGridEdge m) :
    HorizontalCoordinateMarked hm anchor edge.x edge.y <->
      HorizontalEdgeMarked hm anchor edge := by
  constructor
  · rintro ⟨other, x_eq, y_eq, marked⟩
    have same : other = edge :=
      horizontalGridEdge_eq_of_coordinates x_eq y_eq
    simpa [same] using marked
  · intro marked
    exact ⟨edge, rfl, rfl, marked⟩

theorem verticalCoordinateMarked_iff {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (edge : VerticalGridEdge m) :
    VerticalCoordinateMarked hm anchor edge.x edge.y <->
      VerticalEdgeMarked hm anchor edge := by
  constructor
  · rintro ⟨other, x_eq, y_eq, marked⟩
    have same : other = edge :=
      verticalGridEdge_eq_of_coordinates x_eq y_eq
    simpa [same] using marked
  · intro marked
    exact ⟨edge, rfl, rfl, marked⟩

def cellSouthEdge {m : Nat} (cell : GridCell m) : HorizontalGridEdge m where
  x := cell.x
  y := cell.y
  x_lt := cell.x_lt
  y_le := by have h := cell.y_lt; omega

def cellNorthEdge {m : Nat} (cell : GridCell m) : HorizontalGridEdge m where
  x := cell.x
  y := cell.y + 1
  x_lt := cell.x_lt
  y_le := by have h := cell.y_lt; omega

def cellWestEdge {m : Nat} (cell : GridCell m) : VerticalGridEdge m where
  x := cell.x
  y := cell.y
  x_le := by have h := cell.x_lt; omega
  y_lt := cell.y_lt

def cellEastEdge {m : Nat} (cell : GridCell m) : VerticalGridEdge m where
  x := cell.x + 1
  y := cell.y
  x_le := by have h := cell.x_lt; omega
  y_lt := cell.y_lt

theorem cellSouthEdge_represents {m : Nat} (cell : GridCell m) :
    RepresentsHorizontal cell CellSide.south (cellSouthEdge cell) := by
  unfold RepresentsHorizontal SameUndirectedEdge
  left
  constructor <;> apply gridSample_eq_of_coordinates <;>
    simp [cellSouthEdge, sideStart, sideEnd, southWest, southEast,
      horizontalStart, horizontalEnd]

theorem cellNorthEdge_represents {m : Nat} (cell : GridCell m) :
    RepresentsHorizontal cell CellSide.north (cellNorthEdge cell) := by
  unfold RepresentsHorizontal SameUndirectedEdge
  right
  constructor <;> apply gridSample_eq_of_coordinates <;>
    simp [cellNorthEdge, sideStart, sideEnd, northEast, northWest,
      horizontalStart, horizontalEnd]

theorem cellWestEdge_represents {m : Nat} (cell : GridCell m) :
    RepresentsVertical cell CellSide.west (cellWestEdge cell) := by
  unfold RepresentsVertical SameUndirectedEdge
  right
  constructor <;> apply gridSample_eq_of_coordinates <;>
    simp [cellWestEdge, sideStart, sideEnd, northWest, southWest,
      verticalStart, verticalEnd]

theorem cellEastEdge_represents {m : Nat} (cell : GridCell m) :
    RepresentsVertical cell CellSide.east (cellEastEdge cell) := by
  unfold RepresentsVertical SameUndirectedEdge
  left
  constructor <;> apply gridSample_eq_of_coordinates <;>
    simp [cellEastEdge, sideStart, sideEnd, southEast, northEast,
      verticalStart, verticalEnd]

theorem propBool_congr {left right : Prop} (same : left <-> right) :
    propBool left = propBool right := by
  classical
  simp [propBool, same]

noncomputable def orbitRectangularMarking {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) : RectangularEdgeMarking where
  horizontal := fun x y => propBool (HorizontalCoordinateMarked hm anchor x y)
  vertical := fun x y => propBool (VerticalCoordinateMarked hm anchor x y)

theorem orbitMarking_south {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (cell : GridCell m) :
    (orbitRectangularMarking hm anchor).horizontal cell.x cell.y =
      sideMarkBool hm anchor cell CellSide.south := by
  unfold orbitRectangularMarking sideMarkBool
  apply propBool_congr
  exact (horizontalCoordinateMarked_iff hm anchor (cellSouthEdge cell)).trans
    (horizontalEdgeMarked_iff_sideMarked hm anchor cell CellSide.south
      (cellSouthEdge cell) (cellSouthEdge_represents cell))

theorem orbitMarking_north {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (cell : GridCell m) :
    (orbitRectangularMarking hm anchor).horizontal cell.x (cell.y + 1) =
      sideMarkBool hm anchor cell CellSide.north := by
  unfold orbitRectangularMarking sideMarkBool
  apply propBool_congr
  exact (horizontalCoordinateMarked_iff hm anchor (cellNorthEdge cell)).trans
    (horizontalEdgeMarked_iff_sideMarked hm anchor cell CellSide.north
      (cellNorthEdge cell) (cellNorthEdge_represents cell))

theorem orbitMarking_west {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (cell : GridCell m) :
    (orbitRectangularMarking hm anchor).vertical cell.x cell.y =
      sideMarkBool hm anchor cell CellSide.west := by
  unfold orbitRectangularMarking sideMarkBool
  apply propBool_congr
  exact (verticalCoordinateMarked_iff hm anchor (cellWestEdge cell)).trans
    (verticalEdgeMarked_iff_sideMarked hm anchor cell CellSide.west
      (cellWestEdge cell) (cellWestEdge_represents cell))

theorem orbitMarking_east {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (cell : GridCell m) :
    (orbitRectangularMarking hm anchor).vertical (cell.x + 1) cell.y =
      sideMarkBool hm anchor cell CellSide.east := by
  unfold orbitRectangularMarking sideMarkBool
  apply propBool_congr
  exact (verticalCoordinateMarked_iff hm anchor (cellEastEdge cell)).trans
    (verticalEdgeMarked_iff_sideMarked hm anchor cell CellSide.east
      (cellEastEdge cell) (cellEastEdge_represents cell))

theorem orbitRectangularMarking_closed {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) :
    ClosedOn (orbitRectangularMarking hm anchor) (4 * m) (4 * m) := by
  intro x y x_bound y_bound
  let cell : GridCell m := {
    x := x
    y := y
    x_lt := x_bound
    y_lt := y_bound
  }
  unfold CellEven
  change bxor
    (bxor
      ((orbitRectangularMarking hm anchor).horizontal cell.x cell.y)
      ((orbitRectangularMarking hm anchor).vertical (cell.x + 1) cell.y))
    (bxor
      ((orbitRectangularMarking hm anchor).horizontal cell.x (cell.y + 1))
      ((orbitRectangularMarking hm anchor).vertical cell.x cell.y)) = false
  rw [orbitMarking_south, orbitMarking_east,
    orbitMarking_north, orbitMarking_west]
  exact cellSideMark_even hm anchor cell

noncomputable def orbitPotential {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) :
    RectangularPotentialWitness
      (orbitRectangularMarking hm anchor) (4 * m) (4 * m) :=
  closedMarking_hasPotential
    (orbitRectangularMarking hm anchor) (4 * m) (4 * m)
    (orbitRectangularMarking_closed hm anchor)

end ContourOrbitGlobalMarking
end BoundaryOfSelf

#print axioms BoundaryOfSelf.ContourOrbitGlobalMarking.horizontalEdgeMarked_iff_sideMarked
#print axioms BoundaryOfSelf.ContourOrbitGlobalMarking.orbitRectangularMarking_closed
#print axioms BoundaryOfSelf.ContourOrbitGlobalMarking.orbitPotential
