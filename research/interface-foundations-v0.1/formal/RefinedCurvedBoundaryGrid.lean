import CurvedBoundaryGrid

namespace BoundaryOfSelf
namespace RefinedCurvedBoundaryGrid

open CurvedBoundaryGrid

set_option maxRecDepth 100000

abbrev FineAxis := Fin 17

structure FineGridPoint where
  x : FineAxis
  y : FineAxis
deriving DecidableEq, Repr

structure FineGridEdge where
  source : FineGridPoint
  target : FineGridPoint
deriving DecidableEq, Repr

def fineAxes : List FineAxis :=
  List.finRange 17

def fineAxisEdges : List (FineAxis × FineAxis) :=
  (List.finRange 16).map fun i => (i.castSucc, i.succ)

def finePoint (x y : FineAxis) : FineGridPoint :=
  ⟨x, y⟩

def fineEdge (x0 y0 x1 y1 : FineAxis) : FineGridEdge :=
  ⟨finePoint x0 y0, finePoint x1 y1⟩

def fineHorizontalEdges : List FineGridEdge :=
  fineAxes.flatMap fun y =>
    fineAxisEdges.map fun pair => fineEdge pair.1 y pair.2 y

def fineVerticalEdges : List FineGridEdge :=
  fineAxes.flatMap fun x =>
    fineAxisEdges.map fun pair => fineEdge x pair.1 x pair.2

def allFineGridEdges : List FineGridEdge :=
  fineHorizontalEdges ++ fineVerticalEdges

def allFineGridPoints : List FineGridPoint :=
  fineAxes.flatMap fun y => fineAxes.map fun x => finePoint x y

def natDistance (a b : Nat) : Nat :=
  if a <= b then b - a else a - b

def fineRadialTerm (a : FineAxis) : Nat :=
  let d := natDistance a.val 8
  d * d

/-- `fineScalarNumerator p` stores `16 * F(p)` on the quarter-step grid. -/
def fineScalarNumerator (p : FineGridPoint) : Nat :=
  fineRadialTerm p.x + fineRadialTerm p.y

def fineInsideFlag (p : FineGridPoint) : Bool :=
  decide (fineScalarNumerator p <= 32)

def fineCrossesFlag (e : FineGridEdge) : Bool :=
  Bool.xor (fineInsideFlag e.source) (fineInsideFlag e.target)

def fineAdjacentFlag (e : FineGridEdge) : Bool :=
  decide (
    natDistance e.source.x.val e.target.x.val +
      natDistance e.source.y.val e.target.y.val = 1)

def fineInsidePoints : List FineGridPoint :=
  allFineGridPoints.filter fineInsideFlag

def fineContourEdges : List FineGridEdge :=
  allFineGridEdges.filter fineCrossesFlag

def embedAxis : Axis -> FineAxis
  | .a0 => ⟨0, by decide⟩
  | .a1 => ⟨4, by decide⟩
  | .a2 => ⟨8, by decide⟩
  | .a3 => ⟨12, by decide⟩
  | .a4 => ⟨16, by decide⟩

def embedPoint (p : GridPoint) : FineGridPoint :=
  finePoint (embedAxis p.x) (embedAxis p.y)

def coarsenAxis (a : FineAxis) : Axis :=
  match a.val / 4 with
  | 0 => .a0
  | 1 => .a1
  | 2 => .a2
  | 3 => .a3
  | _ => .a4

def coarsenPoint (p : FineGridPoint) : GridPoint :=
  point (coarsenAxis p.x) (coarsenAxis p.y)

def fineUnitDistanceToCoarsening (a : FineAxis) : Nat :=
  natDistance a.val (4 * axisCoordinate (coarsenAxis a))

/-- Distance in quarter-cell units from a fine point to a coarse point. -/
def normalizedPointDistance (p : FineGridPoint) (q : GridPoint) : Nat :=
  max
    (natDistance p.x.val (4 * axisCoordinate q.x))
    (natDistance p.y.val (4 * axisCoordinate q.y))

def coarseContourPoints : List GridPoint :=
  contourEdges.flatMap fun e => [e.source, e.target]

def nearCoarseContour (p : FineGridPoint) : Bool :=
  coarseContourPoints.any fun q => decide (normalizedPointDistance p q <= 4)

def fineEdgeLocalized (e : FineGridEdge) : Bool :=
  nearCoarseContour e.source && nearCoarseContour e.target

theorem fine_grid_has_two_hundred_eighty_nine_points :
    allFineGridPoints.length = 289 := by
  decide

theorem fine_grid_has_five_hundred_forty_four_edges :
    allFineGridEdges.length = 544 := by
  decide

theorem fine_radial_region_has_one_hundred_one_nodes :
    fineInsidePoints.length = 101 := by
  decide

theorem fine_contour_has_forty_four_edges :
    fineContourEdges.length = 44 := by
  decide

theorem fine_contour_all_crossing :
    fineContourEdges.all fineCrossesFlag = true := by
  decide

theorem fine_contour_all_adjacent :
    fineContourEdges.all fineAdjacentFlag = true := by
  decide

theorem fineScalar_on_embedded_coarse (p : GridPoint) :
    fineScalarNumerator (embedPoint p) = 16 * scalarField p := by
  cases p with
  | mk x y =>
      cases x <;> cases y <;> decide

theorem fineInside_on_embedded_coarse (p : GridPoint) :
    fineInsideFlag (embedPoint p) = insideFlag p := by
  cases p with
  | mk x y =>
      cases x <;> cases y <;> decide

theorem coarsen_embedPoint (p : GridPoint) :
    coarsenPoint (embedPoint p) = p := by
  cases p with
  | mk x y =>
      cases x <;> cases y <;> decide

theorem fineAxis_coarsens_within_one_cell :
    ∀ a : FineAxis, fineUnitDistanceToCoarsening a <= 3 := by
  decide

theorem fine_contour_all_localized :
    fineContourEdges.all fineEdgeLocalized = true := by
  decide

theorem fineContourEdge_isAdjacent_and_crosses
    {e : FineGridEdge} (hMember : e ∈ fineContourEdges) :
    fineAdjacentFlag e = true ∧ fineCrossesFlag e = true :=
  ⟨(List.all_eq_true.mp fine_contour_all_adjacent) e hMember,
    (List.all_eq_true.mp fine_contour_all_crossing) e hMember⟩

theorem fineContourEdge_localizes_within_one_coarse_cell
    {e : FineGridEdge} (hMember : e ∈ fineContourEdges) :
    nearCoarseContour e.source = true ∧
      nearCoarseContour e.target = true := by
  have h := (List.all_eq_true.mp fine_contour_all_localized) e hMember
  simpa [fineEdgeLocalized] using h

theorem fineCrossingGridEdge_isReported
    {e : FineGridEdge}
    (hGrid : e ∈ allFineGridEdges)
    (hCrosses : fineCrossesFlag e = true) :
    e ∈ fineContourEdges := by
  simp [fineContourEdges, hGrid, hCrosses]

theorem reportedFineEdge_iff_gridCrossing (e : FineGridEdge) :
    e ∈ fineContourEdges ↔
      e ∈ allFineGridEdges ∧ fineCrossesFlag e = true := by
  simp [fineContourEdges]

end RefinedCurvedBoundaryGrid
end BoundaryOfSelf

#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.fine_grid_has_two_hundred_eighty_nine_points
#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.fine_contour_has_forty_four_edges
#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.fineScalar_on_embedded_coarse
#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.fineInside_on_embedded_coarse
#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.coarsen_embedPoint
#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.fineAxis_coarsens_within_one_cell
#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.fine_contour_all_localized
#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.fineContourEdge_localizes_within_one_coarse_cell
#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.reportedFineEdge_iff_gridCrossing
