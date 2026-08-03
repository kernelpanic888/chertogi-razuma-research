import RectangularParityPotential

namespace BoundaryOfSelf
namespace ContourOrbitLocalParity

open UniformRadialBoundaryFamily
open LocalPolygonalContour
open GlobalContourZeroBoundary
open FiniteAlternatingCycleKernel
open ConcreteRadialContourTraversal

/-!
IF-BS-20C proves the local parity certificate for one alternating contour
orbit. The orbit is closed under both successor and predecessor. A geometric
edge is marked when one of its two cell-side representations lies in the
orbit. Local and shared involutions force the marked sides of every cell to be
either empty or exactly the two threshold-crossing sides.
-/

noncomputable def contourLocalMate {m : Nat} (state : ContourState m) :
    ContourState m :=
  (localInvolution (m := m)).mate state

noncomputable def contourSharedMate {m : Nat} (hm : 0 < m)
    (state : ContourState m) : ContourState m :=
  (sharedInvolution hm).mate state

noncomputable def contourSuccessor {m : Nat} (hm : 0 < m)
    (state : ContourState m) : ContourState m :=
  contourSharedMate hm (contourLocalMate state)

noncomputable def contourPredecessor {m : Nat} (hm : 0 < m)
    (state : ContourState m) : ContourState m :=
  contourLocalMate (contourSharedMate hm state)

inductive SameContourOrbit {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) : ContourState m -> Prop where
  | anchor : SameContourOrbit hm anchor anchor
  | next {state : ContourState m}
      (has : SameContourOrbit hm anchor state) :
      SameContourOrbit hm anchor (contourSuccessor hm state)
  | previous {state : ContourState m}
      (has : SameContourOrbit hm anchor state) :
      SameContourOrbit hm anchor (contourPredecessor hm state)

theorem contourLocalMate_related {m : Nat} (state : ContourState m) :
    LocalPartner state (contourLocalMate state) := by
  exact selectedMate_related LocalPartner localPartner_existsUnique state

theorem contourSharedMate_related {m : Nat} (hm : 0 < m)
    (state : ContourState m) :
    SharedPartner state (contourSharedMate hm state) := by
  exact selectedMate_related SharedPartner
    (sharedPartner_existsUnique hm) state

theorem contourSharedMate_involutive {m : Nat} (hm : 0 < m)
    (state : ContourState m) :
    contourSharedMate hm (contourSharedMate hm state) = state := by
  exact (sharedInvolution hm).involutive state

theorem predecessor_sharedMate {m : Nat} (hm : 0 < m)
    (state : ContourState m) :
    contourPredecessor hm (contourSharedMate hm state) =
      contourLocalMate state := by
  unfold contourPredecessor
  rw [contourSharedMate_involutive]

theorem sharesEdge_state_eq_or_sharedMate {m : Nat} (hm : 0 < m)
    (edgeState state : ContourState m)
    (shares : SharesEdgeWith edgeState state.val) :
    state = edgeState \/ state = contourSharedMate hm edgeState := by
  by_cases same : state = edgeState
  · exact Or.inl same
  · right
    have partner : SharedPartner edgeState state := ⟨shares, same⟩
    change state = selectedMate SharedPartner
      (sharedPartner_existsUnique hm) edgeState
    exact (Classical.choose_spec
      (sharedPartner_existsUnique hm edgeState)).2 state partner

theorem sameCell_state_eq_or_localMate {m : Nat}
    (edgeState state : ContourState m)
    (sameCell : SameCell edgeState state) :
    state = edgeState \/ state = contourLocalMate edgeState := by
  by_cases same : state = edgeState
  · exact Or.inl same
  · right
    have partner : LocalPartner edgeState state := ⟨sameCell, same⟩
    change state = selectedMate LocalPartner
      localPartner_existsUnique edgeState
    exact (Classical.choose_spec
      (localPartner_existsUnique edgeState)).2 state partner

def EdgeMarkedByOrbit {m : Nat} (hm : 0 < m)
    (anchor edgeState : ContourState m) : Prop :=
  exists state, SameContourOrbit hm anchor state /\
    SharesEdgeWith edgeState state.val

theorem orbitState_marks_self {m : Nat} (hm : 0 < m)
    (anchor state : ContourState m)
    (inOrbit : SameContourOrbit hm anchor state) :
    EdgeMarkedByOrbit hm anchor state := by
  exact ⟨state, inOrbit, sharesEdgeWith_self state⟩

theorem edgeMarked_localMate {m : Nat} (hm : 0 < m)
    (anchor edgeState : ContourState m)
    (marked : EdgeMarkedByOrbit hm anchor edgeState) :
    EdgeMarkedByOrbit hm anchor (contourLocalMate edgeState) := by
  rcases marked with ⟨state, state_orbit, shares⟩
  rcases sharesEdge_state_eq_or_sharedMate hm edgeState state shares with
      same | shared
  · subst state
    let next := contourSuccessor hm edgeState
    have next_orbit : SameContourOrbit hm anchor next :=
      SameContourOrbit.next state_orbit
    have next_shares : SharesEdgeWith (contourLocalMate edgeState) next.val := by
      exact (contourSharedMate_related hm (contourLocalMate edgeState)).1
    exact ⟨next, next_orbit, next_shares⟩
  · have previous_orbit :
        SameContourOrbit hm anchor (contourPredecessor hm state) :=
      SameContourOrbit.previous state_orbit
    have previous_eq : contourPredecessor hm state =
        contourLocalMate edgeState := by
      rw [shared, predecessor_sharedMate]
    rw [previous_eq] at previous_orbit
    exact orbitState_marks_self hm anchor (contourLocalMate edgeState)
      previous_orbit

def SideMarkedByOrbit {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (cell : GridCell m) (side : CellSide) : Prop :=
  exists crosses : side ∈ crossingSides cell,
    EdgeMarkedByOrbit hm anchor ⟨(cell, side), crosses⟩

theorem sideMarked_is_crossing {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (cell : GridCell m) (side : CellSide)
    (marked : SideMarkedByOrbit hm anchor cell side) :
    side ∈ crossingSides cell := by
  exact marked.choose

theorem all_crossing_sides_marked_of_one {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (cell : GridCell m) (side : CellSide)
    (marked : SideMarkedByOrbit hm anchor cell side) :
    forall other, other ∈ crossingSides cell ->
      SideMarkedByOrbit hm anchor cell other := by
  rcases marked with ⟨side_crosses, side_marked⟩
  let edgeState : ContourState m := ⟨(cell, side), side_crosses⟩
  have edgeState_marked : EdgeMarkedByOrbit hm anchor edgeState := side_marked
  have mate_marked :
      EdgeMarkedByOrbit hm anchor (contourLocalMate edgeState) :=
    edgeMarked_localMate hm anchor edgeState edgeState_marked
  intro other other_crosses
  let otherState : ContourState m := ⟨(cell, other), other_crosses⟩
  have sameCell : SameCell edgeState otherState := rfl
  rcases sameCell_state_eq_or_localMate edgeState otherState sameCell with
      same | mate
  · have side_eq : other = side :=
      congrArg (fun state : ContourState m => state.val.2) same
    subst other
    exact ⟨side_crosses, edgeState_marked⟩
  · have other_marked : EdgeMarkedByOrbit hm anchor otherState := by
      rw [mate]
      exact mate_marked
    exact ⟨other_crosses, other_marked⟩

theorem sideMarked_iff_crossing_of_one {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (cell : GridCell m) (side : CellSide)
    (marked : SideMarkedByOrbit hm anchor cell side) :
    forall other,
      other ∈ crossingSides cell <->
        SideMarkedByOrbit hm anchor cell other := by
  intro other
  constructor
  · exact all_crossing_sides_marked_of_one hm anchor cell side marked other
  · exact sideMarked_is_crossing hm anchor cell other

def NoMarkedSide {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (cell : GridCell m) : Prop :=
  forall side, ¬ SideMarkedByOrbit hm anchor cell side

theorem cellSideMarks_zero_or_two {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (cell : GridCell m) :
    NoMarkedSide hm anchor cell \/
      Nonempty (ExactlyTwo (SideMarkedByOrbit hm anchor cell)) := by
  by_cases exists_marked : exists side,
      SideMarkedByOrbit hm anchor cell side
  · right
    rcases exists_marked with ⟨side, marked⟩
    let edgeState : ContourState m :=
      ⟨(cell, side), sideMarked_is_crossing hm anchor cell side marked⟩
    exact ⟨transportExactlyTwo (localSidePair edgeState)
      (sideMarked_iff_crossing_of_one hm anchor cell side marked)⟩
  · left
    intro side side_marked
    exact exists_marked ⟨side, side_marked⟩

noncomputable def propBool (P : Prop) : Bool := by
  classical
  exact if P then true else false

theorem propBool_eq_true_iff (P : Prop) : propBool P = true <-> P := by
  classical
  simp [propBool]

noncomputable def sideMarkBool {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (cell : GridCell m) (side : CellSide) : Bool :=
  propBool (SideMarkedByOrbit hm anchor cell side)

theorem exactlyTwo_cellSide_parity (P : CellSide -> Prop)
    (pair : ExactlyTwo P) :
    RectangularParityPotential.bxor
      (RectangularParityPotential.bxor
        (propBool (P CellSide.south)) (propBool (P CellSide.east)))
      (RectangularParityPotential.bxor
        (propBool (P CellSide.north)) (propBool (P CellSide.west))) = false := by
  have exhaustive : forall side,
      P side <-> side = pair.first \/ side = pair.second := by
    intro side
    constructor
    · exact pair.exhaustive side
    · intro has
      rcases has with rfl | rfl
      · exact pair.first_has
      · exact pair.second_has
  have distinct : pair.first ≠ pair.second := pair.distinct
  cases first_eq : pair.first <;> cases second_eq : pair.second <;>
    simp_all [propBool, RectangularParityPotential.bxor]

theorem cellSideMark_even {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) (cell : GridCell m) :
    RectangularParityPotential.bxor
      (RectangularParityPotential.bxor
        (sideMarkBool hm anchor cell CellSide.south)
        (sideMarkBool hm anchor cell CellSide.east))
      (RectangularParityPotential.bxor
        (sideMarkBool hm anchor cell CellSide.north)
        (sideMarkBool hm anchor cell CellSide.west)) = false := by
  rcases cellSideMarks_zero_or_two hm anchor cell with none | pair_exists
  · have south := none CellSide.south
    have east := none CellSide.east
    have north := none CellSide.north
    have west := none CellSide.west
    simp [sideMarkBool, propBool, south, east, north, west,
      RectangularParityPotential.bxor]
  · rcases pair_exists with ⟨pair⟩
    exact exactlyTwo_cellSide_parity
      (SideMarkedByOrbit hm anchor cell) pair

end ContourOrbitLocalParity
end BoundaryOfSelf

#print axioms BoundaryOfSelf.ContourOrbitLocalParity.edgeMarked_localMate
#print axioms BoundaryOfSelf.ContourOrbitLocalParity.all_crossing_sides_marked_of_one
#print axioms BoundaryOfSelf.ContourOrbitLocalParity.cellSideMarks_zero_or_two
#print axioms BoundaryOfSelf.ContourOrbitLocalParity.cellSideMark_even
