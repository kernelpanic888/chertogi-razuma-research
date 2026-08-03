import FiniteAlternatingCycleKernel

namespace BoundaryOfSelf
namespace ConcreteRadialContourTraversal

open UniformRadialBoundaryFamily
open InterpolatedBoundaryContour
open LocalPolygonalContour
open GlobalContourIncidence
open GlobalContourZeroBoundary
open FiniteAlternatingCycleKernel

/-!
IF-BS-15 instantiates the abstract alternating-cycle kernel on the concrete
radial marching-squares contour. A state is a cell-side incidence carrying a
proof that the side crosses the threshold. The local mate uses the other
crossing side of the same cell. The shared mate uses the other cell-side
representation of the same global crossing edge.
-/

abbrev RawLocation (m : Nat) := GridCell m × CellSide

def LocationCrosses {m : Nat} (location : RawLocation m) : Prop :=
  location.2 ∈ crossingSides location.1

def ContourState (m : Nat) :=
  {location : RawLocation m // LocationCrosses location}

instance gridCellDecidableEq {m : Nat} : DecidableEq (GridCell m) :=
  fun a b =>
    if hx : a.x = b.x then
      if hy : a.y = b.y then
        isTrue (gridCell_eq_of_coordinates hx hy)
      else
        isFalse (fun h => hy (congrArg GridCell.y h))
    else
      isFalse (fun h => hx (congrArg GridCell.x h))

noncomputable instance contourStateDecidableEq {m : Nat} :
    DecidableEq (ContourState m) := fun a b =>
  if hCell : a.val.1 = b.val.1 then
    if hSide : a.val.2 = b.val.2 then
      isTrue (Subtype.ext (Prod.ext hCell hSide))
    else
      isFalse (fun h => hSide
        (congrArg (fun state : ContourState m => state.val.2) h))
  else
    isFalse (fun h => hCell
      (congrArg (fun state : ContourState m => state.val.1) h))

instance locationCrossesDecidable {m : Nat} (location : RawLocation m) :
    Decidable (LocationCrosses location) := by
  unfold LocationCrosses
  infer_instance

def SameCell {m : Nat} (a b : ContourState m) : Prop :=
  b.val.1 = a.val.1

def SharesEdgeWith {m : Nat} (a : ContourState m)
    (location : RawLocation m) : Prop :=
  SameUndirectedEdge
    (sideStart location.1 location.2) (sideEnd location.1 location.2)
    (sideStart a.val.1 a.val.2) (sideEnd a.val.1 a.val.2)

def LocalPartner {m : Nat} (a b : ContourState m) : Prop :=
  SameCell a b /\ b ≠ a

def SharedPartner {m : Nat} (a b : ContourState m) : Prop :=
  SharesEdgeWith a b.val /\ b ≠ a

def ExistsUniqueValue {alpha : Type} (P : alpha -> Prop) : Prop :=
  exists value, P value /\ forall candidate, P candidate -> candidate = value

def transportExactlyTwo {alpha : Type} {P Q : alpha -> Prop}
    (pair : ExactlyTwo P) (h : forall x, P x <-> Q x) : ExactlyTwo Q where
  first := pair.first
  second := pair.second
  distinct := pair.distinct
  first_has := (h pair.first).mp pair.first_has
  second_has := (h pair.second).mp pair.second_has
  exhaustive := by
    intro x hx
    exact pair.exhaustive x ((h x).mpr hx)

theorem exactlyTwo_unique_other {alpha : Type} {P : alpha -> Prop}
    (pair : ExactlyTwo P) (a : alpha) (ha : P a) :
    ExistsUniqueValue (fun b => P b /\ b ≠ a) := by
  rcases pair.exhaustive a ha with haFirst | haSecond
  · refine ⟨pair.second, ⟨pair.second_has, ?_⟩, ?_⟩
    · intro hEqual
      apply pair.distinct
      calc
        pair.first = a := haFirst.symm
        _ = pair.second := hEqual.symm
    · intro b hb
      rcases pair.exhaustive b hb.1 with hbFirst | hbSecond
      · exfalso
        apply hb.2
        calc
          b = pair.first := hbFirst
          _ = a := haFirst.symm
      · exact hbSecond
  · refine ⟨pair.first, ⟨pair.first_has, ?_⟩, ?_⟩
    · intro hEqual
      apply pair.distinct
      calc
        pair.first = a := hEqual
        _ = pair.second := haSecond
    · intro b hb
      rcases pair.exhaustive b hb.1 with hbFirst | hbSecond
      · exact hbFirst
      · exfalso
        apply hb.2
        calc
          b = pair.second := hbSecond
          _ = a := haSecond.symm

theorem crossingSides_nodup {m : Nat} (c : GridCell m) :
    (crossingSides c).Nodup := by
  unfold crossingSides
  exact (by decide : allSides.Nodup).filter _

def listExactlyTwo {alpha : Type} (values : List alpha)
    (hLength : values.length = 2) (hNodup : values.Nodup) :
    ExactlyTwo (fun x => x ∈ values) := by
  cases values with
  | nil => simp at hLength
  | cons first tail =>
      cases tail with
      | nil => simp at hLength
      | cons second rest =>
          cases rest with
          | nil =>
              have hDistinct : first ≠ second := by
                intro hEqual
                subst second
                simp at hNodup
              refine {
                first := first
                second := second
                distinct := hDistinct
                first_has := by simp
                second_has := by simp
                exhaustive := ?_
              }
              intro x hx
              simpa using hx
          | cons third rest =>
              simp at hLength

def localSidePair {m : Nat} (a : ContourState m) :
    ExactlyTwo (fun side => side ∈ crossingSides a.val.1) := by
  have hActive : ActiveCell a.val.1 :=
    List.length_pos_of_mem a.property
  exact listExactlyTwo (crossingSides a.val.1)
    (activeCell_has_exactly_two_sides a.val.1 hActive)
    (crossingSides_nodup a.val.1)

def localStatesExactlyTwo {m : Nat} (a : ContourState m) :
    ExactlyTwo (SameCell a) := by
  let pair := localSidePair a
  let firstState : ContourState m :=
    ⟨(a.val.1, pair.first), pair.first_has⟩
  let secondState : ContourState m :=
    ⟨(a.val.1, pair.second), pair.second_has⟩
  refine {
    first := firstState
    second := secondState
    distinct := ?_
    first_has := rfl
    second_has := rfl
    exhaustive := ?_
  }
  · intro hEqual
    apply pair.distinct
    exact congrArg (fun state : ContourState m => state.val.2) hEqual
  · intro b hCell
    have hSide : b.val.2 ∈ crossingSides a.val.1 := by
      have hb := b.property
      unfold LocationCrosses at hb
      rw [hCell] at hb
      exact hb
    rcases pair.exhaustive b.val.2 hSide with hFirst | hSecond
    · left
      apply Subtype.ext
      apply Prod.ext
      · exact hCell
      · exact hFirst
    · right
      apply Subtype.ext
      apply Prod.ext
      · exact hCell
      · exact hSecond

theorem localPartner_existsUnique {m : Nat} (a : ContourState m) :
    ExistsUniqueValue (LocalPartner a) := by
  exact exactlyTwo_unique_other (localStatesExactlyTwo a) a rfl

theorem localPartner_symmetric {m : Nat} {a b : ContourState m}
    (h : LocalPartner a b) : LocalPartner b a := by
  exact ⟨h.1.symm, fun hab => h.2 hab.symm⟩

theorem localPartner_irreflexive {m : Nat} (a : ContourState m) :
    ¬ LocalPartner a a := by
  intro h
  exact h.2 rfl

theorem sameUndirectedEdge_refl {m : Nat} (p q : GridSample m) :
    SameUndirectedEdge p q p q := by
  exact Or.inl ⟨rfl, rfl⟩

theorem sameUndirectedEdge_symm {m : Nat} {p q r s : GridSample m}
    (h : SameUndirectedEdge p q r s) : SameUndirectedEdge r s p q := by
  rcases h with ⟨hpr, hqs⟩ | ⟨hps, hqr⟩
  · exact Or.inl ⟨hpr.symm, hqs.symm⟩
  · exact Or.inr ⟨hqr.symm, hps.symm⟩

theorem sameUndirectedEdge_trans {m : Nat}
    {p q r s u v : GridSample m}
    (hFirst : SameUndirectedEdge p q r s)
    (hSecond : SameUndirectedEdge r s u v) :
    SameUndirectedEdge p q u v := by
  rcases hFirst with ⟨hpr, hqs⟩ | ⟨hps, hqr⟩ <;>
  rcases hSecond with ⟨hru, hsv⟩ | ⟨hrv, hsu⟩
  · exact Or.inl ⟨hpr.trans hru, hqs.trans hsv⟩
  · exact Or.inr ⟨hpr.trans hrv, hqs.trans hsu⟩
  · exact Or.inr ⟨hps.trans hsv, hqr.trans hru⟩
  · exact Or.inl ⟨hps.trans hsu, hqr.trans hrv⟩

theorem crosses_of_sameUndirectedEdge {m : Nat}
    {p q r s : GridSample m} (hSame : SameUndirectedEdge p q r s)
    (hCrosses : Crosses r s) : Crosses p q := by
  rcases hSame with ⟨hpr, hqs⟩ | ⟨hps, hqr⟩
  · simpa [hpr, hqs] using hCrosses
  · have hReverse := crosses_comm hCrosses
    simpa [hps, hqr] using hReverse

def horizontalSharedLocations {m : Nat} (hm : 0 < m)
    (a : ContourState m) (e : HorizontalGridEdge m)
    (hCrosses : HorizontalCrosses e)
    (hRep : RepresentsHorizontal a.val.1 a.val.2 e) :
    ExactlyTwo (SharesEdgeWith a) := by
  have pair := horizontal_exactly_two_incidences hm e hCrosses
  apply transportExactlyTwo pair
  intro location
  constructor
  · intro hLocation
    unfold HorizontalIncident RepresentsHorizontal at hLocation
    unfold RepresentsHorizontal at hRep
    exact sameUndirectedEdge_trans hLocation
      (sameUndirectedEdge_symm hRep)
  · intro hLocation
    unfold HorizontalIncident RepresentsHorizontal
    unfold RepresentsHorizontal at hRep
    exact sameUndirectedEdge_trans hLocation hRep

def verticalSharedLocations {m : Nat} (hm : 0 < m)
    (a : ContourState m) (e : VerticalGridEdge m)
    (hCrosses : VerticalCrosses e)
    (hRep : RepresentsVertical a.val.1 a.val.2 e) :
    ExactlyTwo (SharesEdgeWith a) := by
  have pair := vertical_exactly_two_incidences hm e hCrosses
  apply transportExactlyTwo pair
  intro location
  constructor
  · intro hLocation
    unfold VerticalIncident RepresentsVertical at hLocation
    unfold RepresentsVertical at hRep
    exact sameUndirectedEdge_trans hLocation
      (sameUndirectedEdge_symm hRep)
  · intro hLocation
    unfold VerticalIncident RepresentsVertical
    unfold RepresentsVertical at hRep
    exact sameUndirectedEdge_trans hLocation hRep

def sharedLocationsExactlyTwo {m : Nat} (hm : 0 < m)
    (a : ContourState m) : ExactlyTwo (SharesEdgeWith a) := by
  rcases a with ⟨⟨c, side⟩, hSide⟩
  have hSideCrosses : Crosses (sideStart c side) (sideEnd c side) :=
    (sideCrossingFlag_eq_true_iff c side).mp
      ((mem_crossingSides_iff c side).mp hSide)
  cases side with
  | south =>
      let e : HorizontalGridEdge m := {
        x := c.x
        y := c.y
        x_lt := c.x_lt
        y_le := by have h := c.y_lt; omega
      }
      have hCrosses : HorizontalCrosses e := by
        simpa [HorizontalCrosses, e, horizontalStart, horizontalEnd,
          sideStart, sideEnd, southWest, southEast] using hSideCrosses
      have hRep : RepresentsHorizontal c CellSide.south e := by
        unfold RepresentsHorizontal SameUndirectedEdge
        left
        constructor <;> apply gridSample_eq_of_coordinates <;>
          simp [e, sideStart, sideEnd, southWest, southEast,
            horizontalStart, horizontalEnd]
      exact horizontalSharedLocations hm ⟨(c, CellSide.south), hSide⟩
        e hCrosses hRep
  | east =>
      let e : VerticalGridEdge m := {
        x := c.x + 1
        y := c.y
        x_le := by have h := c.x_lt; omega
        y_lt := c.y_lt
      }
      have hCrosses : VerticalCrosses e := by
        simpa [VerticalCrosses, e, verticalStart, verticalEnd,
          sideStart, sideEnd, southEast, northEast] using hSideCrosses
      have hRep : RepresentsVertical c CellSide.east e := by
        unfold RepresentsVertical SameUndirectedEdge
        left
        constructor <;> apply gridSample_eq_of_coordinates <;>
          simp [e, sideStart, sideEnd, southEast, northEast,
            verticalStart, verticalEnd]
      exact verticalSharedLocations hm ⟨(c, CellSide.east), hSide⟩
        e hCrosses hRep
  | north =>
      let e : HorizontalGridEdge m := {
        x := c.x
        y := c.y + 1
        x_lt := c.x_lt
        y_le := by have h := c.y_lt; omega
      }
      have hCrosses : HorizontalCrosses e := by
        have hReverse := crosses_comm hSideCrosses
        simpa [HorizontalCrosses, e, horizontalStart, horizontalEnd,
          sideStart, sideEnd, northEast, northWest] using hReverse
      have hRep : RepresentsHorizontal c CellSide.north e := by
        unfold RepresentsHorizontal SameUndirectedEdge
        right
        constructor <;> apply gridSample_eq_of_coordinates <;>
          simp [e, sideStart, sideEnd, northEast, northWest,
            horizontalStart, horizontalEnd]
      exact horizontalSharedLocations hm ⟨(c, CellSide.north), hSide⟩
        e hCrosses hRep
  | west =>
      let e : VerticalGridEdge m := {
        x := c.x
        y := c.y
        x_le := by have h := c.x_lt; omega
        y_lt := c.y_lt
      }
      have hCrosses : VerticalCrosses e := by
        have hReverse := crosses_comm hSideCrosses
        simpa [VerticalCrosses, e, verticalStart, verticalEnd,
          sideStart, sideEnd, northWest, southWest] using hReverse
      have hRep : RepresentsVertical c CellSide.west e := by
        unfold RepresentsVertical SameUndirectedEdge
        right
        constructor <;> apply gridSample_eq_of_coordinates <;>
          simp [e, sideStart, sideEnd, northWest, southWest,
            verticalStart, verticalEnd]
      exact verticalSharedLocations hm ⟨(c, CellSide.west), hSide⟩
        e hCrosses hRep

theorem sharedLocation_crosses {m : Nat} (a : ContourState m)
    (location : RawLocation m) (hShared : SharesEdgeWith a location) :
    LocationCrosses location := by
  have hAnchorCrosses :
      Crosses (sideStart a.val.1 a.val.2) (sideEnd a.val.1 a.val.2) :=
    (sideCrossingFlag_eq_true_iff a.val.1 a.val.2).mp
      ((mem_crossingSides_iff a.val.1 a.val.2).mp a.property)
  have hLocationCrosses := crosses_of_sameUndirectedEdge hShared hAnchorCrosses
  exact (mem_crossingSides_iff location.1 location.2).mpr
    ((sideCrossingFlag_eq_true_iff location.1 location.2).mpr hLocationCrosses)

def sharedStatesExactlyTwo {m : Nat} (hm : 0 < m)
    (a : ContourState m) :
    ExactlyTwo (fun b : ContourState m => SharesEdgeWith a b.val) := by
  let pair := sharedLocationsExactlyTwo hm a
  let firstState : ContourState m :=
    ⟨pair.first, sharedLocation_crosses a pair.first pair.first_has⟩
  let secondState : ContourState m :=
    ⟨pair.second, sharedLocation_crosses a pair.second pair.second_has⟩
  refine {
    first := firstState
    second := secondState
    distinct := ?_
    first_has := pair.first_has
    second_has := pair.second_has
    exhaustive := ?_
  }
  · intro hEqual
    apply pair.distinct
    exact congrArg Subtype.val hEqual
  · intro b hShared
    rcases pair.exhaustive b.val hShared with hFirst | hSecond
    · left
      exact Subtype.ext hFirst
    · right
      exact Subtype.ext hSecond

theorem sharesEdgeWith_self {m : Nat} (a : ContourState m) :
    SharesEdgeWith a a.val := by
  exact sameUndirectedEdge_refl _ _

theorem sharedPartner_existsUnique {m : Nat} (hm : 0 < m)
    (a : ContourState m) : ExistsUniqueValue (SharedPartner a) := by
  exact exactlyTwo_unique_other (sharedStatesExactlyTwo hm a) a
    (sharesEdgeWith_self a)

theorem sharedPartner_symmetric {m : Nat} {a b : ContourState m}
    (h : SharedPartner a b) : SharedPartner b a := by
  refine ⟨sameUndirectedEdge_symm h.1, ?_⟩
  intro hab
  exact h.2 hab.symm

theorem sharedPartner_irreflexive {m : Nat} (a : ContourState m) :
    ¬ SharedPartner a a := by
  intro h
  exact h.2 rfl

noncomputable def selectedMate {alpha : Type} (R : alpha -> alpha -> Prop)
    (hUnique : forall a, ExistsUniqueValue (R a)) (a : alpha) : alpha :=
  Classical.choose (hUnique a)

theorem selectedMate_related {alpha : Type} (R : alpha -> alpha -> Prop)
    (hUnique : forall a, ExistsUniqueValue (R a)) (a : alpha) :
    R a (selectedMate R hUnique a) :=
  (Classical.choose_spec (hUnique a)).1

noncomputable def involutionOfUniqueSymmetric {alpha : Type}
    (R : alpha -> alpha -> Prop)
    (hUnique : forall a, ExistsUniqueValue (R a))
    (hSymmetric : forall {a b}, R a b -> R b a)
    (hIrreflexive : forall a, ¬ R a a) :
    FixedPointFreeInvolution alpha where
  mate := selectedMate R hUnique
  involutive := by
    intro a
    have hForward := selectedMate_related R hUnique a
    have hBackward := hSymmetric hForward
    have hChosen := Classical.choose_spec
      (hUnique (selectedMate R hUnique a))
    exact (hChosen.2 a hBackward).symm
  no_fixed_point := by
    intro a hFixed
    have hRelated := selectedMate_related R hUnique a
    rw [hFixed] at hRelated
    exact hIrreflexive a hRelated

noncomputable def localInvolution {m : Nat} :
    FixedPointFreeInvolution (ContourState m) :=
  involutionOfUniqueSymmetric LocalPartner
    localPartner_existsUnique localPartner_symmetric localPartner_irreflexive

noncomputable def sharedInvolution {m : Nat} (hm : 0 < m) :
    FixedPointFreeInvolution (ContourState m) :=
  involutionOfUniqueSymmetric SharedPartner
    (sharedPartner_existsUnique hm) sharedPartner_symmetric
    sharedPartner_irreflexive

def allGridCells (m : Nat) : List (GridCell m) :=
  (List.range (4 * m)).attach.flatMap fun x =>
    (List.range (4 * m)).attach.map fun y => {
      x := x.val
      y := y.val
      x_lt := List.mem_range.mp x.property
      y_lt := List.mem_range.mp y.property
    }

theorem allGridCells_covers {m : Nat} (c : GridCell m) :
    c ∈ allGridCells m := by
  unfold allGridCells
  apply List.mem_flatMap.mpr
  let x : {n // n ∈ List.range (4 * m)} :=
    ⟨c.x, List.mem_range.mpr c.x_lt⟩
  let y : {n // n ∈ List.range (4 * m)} :=
    ⟨c.y, List.mem_range.mpr c.y_lt⟩
  refine ⟨x, List.mem_attach _ x, ?_⟩
  apply List.mem_map.mpr
  refine ⟨y, List.mem_attach _ y, ?_⟩
  apply gridCell_eq_of_coordinates <;> rfl

def allRawLocations (m : Nat) : List (RawLocation m) :=
  (allGridCells m).flatMap fun c =>
    allSides.map fun side => (c, side)

theorem allRawLocations_covers {m : Nat} (location : RawLocation m) :
    location ∈ allRawLocations m := by
  rcases location with ⟨c, side⟩
  unfold allRawLocations
  apply List.mem_flatMap.mpr
  refine ⟨c, allGridCells_covers c, ?_⟩
  cases side <;> simp [allSides]

def collectContourStates {m : Nat} :
    List (RawLocation m) -> List (ContourState m)
  | [] => []
  | location :: tail =>
      if h : LocationCrosses location then
        ⟨location, h⟩ :: collectContourStates tail
      else
        collectContourStates tail

theorem mem_collectContourStates {m : Nat} (state : ContourState m)
    (locations : List (RawLocation m)) (hMem : state.val ∈ locations) :
    state ∈ collectContourStates locations := by
  induction locations with
  | nil => simp at hMem
  | cons head tail ih =>
      simp only [collectContourStates]
      split
      case isTrue hCrosses =>
        rcases List.mem_cons.mp hMem with hHead | hTail
        · apply List.mem_cons.mpr
          left
          apply Subtype.ext
          exact hHead
        · apply List.mem_cons.mpr
          right
          exact ih hTail
      case isFalse hNotCrosses =>
        rcases List.mem_cons.mp hMem with hHead | hTail
        · have : LocationCrosses head := by
            simpa [hHead] using state.property
          exact False.elim (hNotCrosses this)
        · exact ih hTail

def contourStateCover (m : Nat) : List (ContourState m) :=
  collectContourStates (allRawLocations m)

theorem contourStateCover_covers {m : Nat} (state : ContourState m) :
    state ∈ contourStateCover m := by
  apply mem_collectContourStates
  exact allRawLocations_covers state.val

noncomputable def radialContourTraversal {m : Nat} (hm : 0 < m) :
    FiniteAlternatingTraversal (ContourState m) where
  localMate := localInvolution
  sharedMate := sharedInvolution hm
  cover := contourStateCover m
  covers := contourStateCover_covers

theorem every_radial_contour_state_has_closed_cycle {m : Nat}
    (hm : 0 < m) (state : ContourState m) :
    exists period : Nat, 0 < period /\
      iterate
        (successor (localInvolution (m := m)) (sharedInvolution hm))
        period state = state := by
  exact every_state_has_closed_cycle (radialContourTraversal hm) state

end ConcreteRadialContourTraversal
end BoundaryOfSelf
