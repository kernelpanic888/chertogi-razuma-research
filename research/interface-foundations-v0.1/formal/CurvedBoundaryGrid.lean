import RationalBoundaryLimit

namespace BoundaryOfSelf
namespace CurvedBoundaryGrid

inductive Axis where
  | a0
  | a1
  | a2
  | a3
  | a4
deriving DecidableEq, Repr

structure GridPoint where
  x : Axis
  y : Axis
deriving DecidableEq, Repr

structure GridEdge where
  source : GridPoint
  target : GridPoint
deriving DecidableEq, Repr

def axes : List Axis :=
  [.a0, .a1, .a2, .a3, .a4]

def axisEdges : List (Axis × Axis) :=
  [(.a0, .a1), (.a1, .a2), (.a2, .a3), (.a3, .a4)]

def point (x y : Axis) : GridPoint :=
  ⟨x, y⟩

def edge (x0 y0 x1 y1 : Axis) : GridEdge :=
  ⟨point x0 y0, point x1 y1⟩

def horizontalEdges : List GridEdge :=
  axes.flatMap fun y =>
    axisEdges.map fun pair => edge pair.1 y pair.2 y

def verticalEdges : List GridEdge :=
  axes.flatMap fun x =>
    axisEdges.map fun pair => edge x pair.1 x pair.2

def allGridEdges : List GridEdge :=
  horizontalEdges ++ verticalEdges

def allGridPoints : List GridPoint :=
  axes.flatMap fun y => axes.map fun x => point x y

def radialTerm : Axis -> Nat
  | .a0 => 4
  | .a1 => 1
  | .a2 => 0
  | .a3 => 1
  | .a4 => 4

def scalarField (p : GridPoint) : Nat :=
  radialTerm p.x + radialTerm p.y

def insideFlag (p : GridPoint) : Bool :=
  decide (scalarField p <= 2)

def crossesFlag (e : GridEdge) : Bool :=
  Bool.xor (insideFlag e.source) (insideFlag e.target)

def axisCoordinate : Axis -> Nat
  | .a0 => 0
  | .a1 => 1
  | .a2 => 2
  | .a3 => 3
  | .a4 => 4

def axisDistance (a b : Axis) : Nat :=
  if axisCoordinate a <= axisCoordinate b then
    axisCoordinate b - axisCoordinate a
  else
    axisCoordinate a - axisCoordinate b

def adjacentFlag (e : GridEdge) : Bool :=
  decide (
    axisDistance e.source.x e.target.x +
      axisDistance e.source.y e.target.y = 1)

def insidePoints : List GridPoint :=
  allGridPoints.filter insideFlag

def contourEdges : List GridEdge :=
  allGridEdges.filter crossesFlag

theorem grid_has_twenty_five_points :
    allGridPoints.length = 25 := by
  decide

theorem grid_has_forty_edges :
    allGridEdges.length = 40 := by
  decide

theorem radial_region_has_nine_nodes :
    insidePoints.length = 9 := by
  decide

theorem contour_has_twelve_edges :
    contourEdges.length = 12 := by
  decide

theorem contour_all_crossing :
    contourEdges.all crossesFlag = true := by
  decide

theorem contour_all_adjacent :
    contourEdges.all adjacentFlag = true := by
  decide

theorem contourEdge_crosses
    {e : GridEdge} (hMember : e ∈ contourEdges) :
    crossesFlag e = true :=
  (List.all_eq_true.mp contour_all_crossing) e hMember

theorem contourEdge_isAdjacent
    {e : GridEdge} (hMember : e ∈ contourEdges) :
    adjacentFlag e = true :=
  (List.all_eq_true.mp contour_all_adjacent) e hMember

theorem contourEdge_isAdjacent_and_crosses
    {e : GridEdge} (hMember : e ∈ contourEdges) :
    adjacentFlag e = true ∧ crossesFlag e = true :=
  ⟨contourEdge_isAdjacent hMember, contourEdge_crosses hMember⟩

theorem crossingGridEdge_isReported
    {e : GridEdge}
    (hGrid : e ∈ allGridEdges)
    (hCrosses : crossesFlag e = true) :
    e ∈ contourEdges := by
  simp [contourEdges, hGrid, hCrosses]

theorem reportedEdge_iff_gridCrossing
    (e : GridEdge) :
    e ∈ contourEdges <->
      e ∈ allGridEdges /\ crossesFlag e = true := by
  simp [contourEdges]

end CurvedBoundaryGrid
end BoundaryOfSelf

#print axioms BoundaryOfSelf.CurvedBoundaryGrid.contour_has_twelve_edges
#print axioms BoundaryOfSelf.CurvedBoundaryGrid.contour_all_crossing
#print axioms BoundaryOfSelf.CurvedBoundaryGrid.contourEdge_crosses
#print axioms BoundaryOfSelf.CurvedBoundaryGrid.contourEdge_isAdjacent_and_crosses
#print axioms BoundaryOfSelf.CurvedBoundaryGrid.crossingGridEdge_isReported
#print axioms BoundaryOfSelf.CurvedBoundaryGrid.reportedEdge_iff_gridCrossing
