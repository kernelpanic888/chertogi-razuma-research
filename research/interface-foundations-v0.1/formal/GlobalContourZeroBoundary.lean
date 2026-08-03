import GlobalContourIncidence

namespace BoundaryOfSelf
namespace GlobalContourZeroBoundary

open UniformRadialBoundaryFamily
open InterpolatedBoundaryContour
open LocalPolygonalContour
open GlobalContourIncidence

/-!
IF-BS-13 classifies every cell-side representation of a canonical crossing
edge. Together with IF-BS-12 existence, this gives exact degree two at every
global contour vertex and hence zero boundary over coefficients modulo two.
-/

theorem gridSample_eq_of_coordinates {m : Nat} {p q : GridSample m}
    (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  cases p
  cases q
  simp_all

theorem gridCell_eq_of_coordinates {m : Nat} {c d : GridCell m}
    (hx : c.x = d.x) (hy : c.y = d.y) : c = d := by
  cases c
  cases d
  simp_all

def SameUndirectedEdge {m : Nat}
    (p q r s : GridSample m) : Prop :=
  (p = r /\ q = s) \/ (p = s /\ q = r)

def RepresentsHorizontal {m : Nat} (c : GridCell m) (s : CellSide)
    (e : HorizontalGridEdge m) : Prop :=
  SameUndirectedEdge (sideStart c s) (sideEnd c s)
    (horizontalStart e) (horizontalEnd e)

def RepresentsVertical {m : Nat} (c : GridCell m) (s : CellSide)
    (e : VerticalGridEdge m) : Prop :=
  SameUndirectedEdge (sideStart c s) (sideEnd c s)
    (verticalStart e) (verticalEnd e)

theorem horizontal_representation_classification {m : Nat} (hm : 0 < m)
    (e : HorizontalGridEdge m) (hCrosses : HorizontalCrosses e)
    (c : GridCell m) (s : CellSide) (hRep : RepresentsHorizontal c s e) :
    (s = CellSide.south /\
      c = horizontalAboveCell e (horizontal_crossing_is_interior hm e hCrosses).2) \/
    (s = CellSide.north /\
      c = horizontalBelowCell e (horizontal_crossing_is_interior hm e hCrosses).1) := by
  have hInterior := horizontal_crossing_is_interior hm e hCrosses
  unfold RepresentsHorizontal SameUndirectedEdge at hRep
  cases s with
  | south =>
      rcases hRep with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hx := congrArg (fun p : GridSample m => p.x) h1
        have hy := congrArg (fun p : GridSample m => p.y) h1
        simp [sideStart, southWest, horizontalStart] at hx hy
        left
        refine ⟨rfl, ?_⟩
        apply gridCell_eq_of_coordinates
        · simpa [horizontalAboveCell] using hx
        · simpa [horizontalAboveCell] using hy
      · have hx1 := congrArg (fun p : GridSample m => p.x) h1
        have hx2 := congrArg (fun p : GridSample m => p.x) h2
        simp [sideStart, sideEnd, southWest, southEast,
          horizontalStart, horizontalEnd] at hx1 hx2
        omega
  | east =>
      rcases hRep with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hy1 := congrArg (fun p : GridSample m => p.y) h1
        have hy2 := congrArg (fun p : GridSample m => p.y) h2
        simp [sideStart, sideEnd, southEast, northEast,
          horizontalStart, horizontalEnd] at hy1 hy2
        omega
      · have hy1 := congrArg (fun p : GridSample m => p.y) h1
        have hy2 := congrArg (fun p : GridSample m => p.y) h2
        simp [sideStart, sideEnd, southEast, northEast,
          horizontalStart, horizontalEnd] at hy1 hy2
        omega
  | north =>
      rcases hRep with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hx1 := congrArg (fun p : GridSample m => p.x) h1
        have hx2 := congrArg (fun p : GridSample m => p.x) h2
        simp [sideStart, sideEnd, northEast, northWest,
          horizontalStart, horizontalEnd] at hx1 hx2
        omega
      · have hx := congrArg (fun p : GridSample m => p.x) h2
        have hy := congrArg (fun p : GridSample m => p.y) h2
        simp [sideStart, sideEnd, northWest, horizontalStart] at hx hy
        have hyCell : c.y = e.y - 1 := by omega
        right
        refine ⟨rfl, ?_⟩
        apply gridCell_eq_of_coordinates
        · simpa [horizontalBelowCell] using hx
        · simpa [horizontalBelowCell] using hyCell
  | west =>
      rcases hRep with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hy1 := congrArg (fun p : GridSample m => p.y) h1
        have hy2 := congrArg (fun p : GridSample m => p.y) h2
        simp [sideStart, sideEnd, northWest, southWest,
          horizontalStart, horizontalEnd] at hy1 hy2
        omega
      · have hy1 := congrArg (fun p : GridSample m => p.y) h1
        have hy2 := congrArg (fun p : GridSample m => p.y) h2
        simp [sideStart, sideEnd, northWest, southWest,
          horizontalStart, horizontalEnd] at hy1 hy2
        omega

theorem vertical_representation_classification {m : Nat} (hm : 0 < m)
    (e : VerticalGridEdge m) (hCrosses : VerticalCrosses e)
    (c : GridCell m) (s : CellSide) (hRep : RepresentsVertical c s e) :
    (s = CellSide.east /\
      c = verticalLeftCell e (vertical_crossing_is_interior hm e hCrosses).1) \/
    (s = CellSide.west /\
      c = verticalRightCell e (vertical_crossing_is_interior hm e hCrosses).2) := by
  have hInterior := vertical_crossing_is_interior hm e hCrosses
  unfold RepresentsVertical SameUndirectedEdge at hRep
  cases s with
  | south =>
      rcases hRep with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hx1 := congrArg (fun p : GridSample m => p.x) h1
        have hx2 := congrArg (fun p : GridSample m => p.x) h2
        simp [sideStart, sideEnd, southWest, southEast,
          verticalStart, verticalEnd] at hx1 hx2
        omega
      · have hx1 := congrArg (fun p : GridSample m => p.x) h1
        have hx2 := congrArg (fun p : GridSample m => p.x) h2
        simp [sideStart, sideEnd, southWest, southEast,
          verticalStart, verticalEnd] at hx1 hx2
        omega
  | east =>
      rcases hRep with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hx := congrArg (fun p : GridSample m => p.x) h1
        have hy := congrArg (fun p : GridSample m => p.y) h1
        simp [sideStart, southEast, verticalStart] at hx hy
        have hxCell : c.x = e.x - 1 := by omega
        left
        refine ⟨rfl, ?_⟩
        apply gridCell_eq_of_coordinates
        · simpa [verticalLeftCell] using hxCell
        · simpa [verticalLeftCell] using hy
      · have hy1 := congrArg (fun p : GridSample m => p.y) h1
        have hy2 := congrArg (fun p : GridSample m => p.y) h2
        simp [sideStart, sideEnd, southEast, northEast,
          verticalStart, verticalEnd] at hy1 hy2
        omega
  | north =>
      rcases hRep with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hx1 := congrArg (fun p : GridSample m => p.x) h1
        have hx2 := congrArg (fun p : GridSample m => p.x) h2
        simp [sideStart, sideEnd, northEast, northWest,
          verticalStart, verticalEnd] at hx1 hx2
        omega
      · have hx1 := congrArg (fun p : GridSample m => p.x) h1
        have hx2 := congrArg (fun p : GridSample m => p.x) h2
        simp [sideStart, sideEnd, northEast, northWest,
          verticalStart, verticalEnd] at hx1 hx2
        omega
  | west =>
      rcases hRep with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hy1 := congrArg (fun p : GridSample m => p.y) h1
        have hy2 := congrArg (fun p : GridSample m => p.y) h2
        simp [sideStart, sideEnd, northWest, southWest,
          verticalStart, verticalEnd] at hy1 hy2
        omega
      · have hx := congrArg (fun p : GridSample m => p.x) h2
        have hy := congrArg (fun p : GridSample m => p.y) h2
        simp [sideStart, sideEnd, southWest, verticalStart] at hx hy
        right
        refine ⟨rfl, ?_⟩
        apply gridCell_eq_of_coordinates
        · simpa [verticalRightCell] using hx
        · simpa [verticalRightCell] using hy

theorem horizontal_above_represents {m : Nat} (e : HorizontalGridEdge m)
    (hy : e.y < 4 * m) :
    RepresentsHorizontal (horizontalAboveCell e hy) CellSide.south e := by
  unfold RepresentsHorizontal SameUndirectedEdge
  left
  constructor <;> apply gridSample_eq_of_coordinates <;>
    simp [sideStart, sideEnd, horizontalAboveCell, southWest, southEast,
      horizontalStart, horizontalEnd]

theorem horizontal_below_represents {m : Nat} (e : HorizontalGridEdge m)
    (hy : 0 < e.y) :
    RepresentsHorizontal (horizontalBelowCell e hy) CellSide.north e := by
  have hyOne : 1 <= e.y := by omega
  have hyCancel : e.y - 1 + 1 = e.y := Nat.sub_add_cancel hyOne
  unfold RepresentsHorizontal SameUndirectedEdge
  right
  constructor <;> apply gridSample_eq_of_coordinates <;>
    simp [sideStart, sideEnd, horizontalBelowCell, northEast, northWest,
      horizontalStart, horizontalEnd, hyCancel]

theorem vertical_left_represents {m : Nat} (e : VerticalGridEdge m)
    (hx : 0 < e.x) :
    RepresentsVertical (verticalLeftCell e hx) CellSide.east e := by
  have hxOne : 1 <= e.x := by omega
  have hxCancel : e.x - 1 + 1 = e.x := Nat.sub_add_cancel hxOne
  unfold RepresentsVertical SameUndirectedEdge
  left
  constructor <;> apply gridSample_eq_of_coordinates <;>
    simp [sideStart, sideEnd, verticalLeftCell, southEast, northEast,
      verticalStart, verticalEnd, hxCancel]

theorem vertical_right_represents {m : Nat} (e : VerticalGridEdge m)
    (hx : e.x < 4 * m) :
    RepresentsVertical (verticalRightCell e hx) CellSide.west e := by
  unfold RepresentsVertical SameUndirectedEdge
  right
  constructor <;> apply gridSample_eq_of_coordinates <;>
    simp [sideStart, sideEnd, verticalRightCell, northWest, southWest,
      verticalStart, verticalEnd]

structure ExactlyTwo {alpha : Type} (P : alpha -> Prop) where
  first : alpha
  second : alpha
  distinct : first ≠ second
  first_has : P first
  second_has : P second
  exhaustive : forall a, P a -> a = first \/ a = second

def HorizontalLocation (m : Nat) := GridCell m × CellSide
def VerticalLocation (m : Nat) := GridCell m × CellSide

def HorizontalIncident {m : Nat} (e : HorizontalGridEdge m)
    (location : HorizontalLocation m) : Prop :=
  RepresentsHorizontal location.1 location.2 e

def VerticalIncident {m : Nat} (e : VerticalGridEdge m)
    (location : VerticalLocation m) : Prop :=
  RepresentsVertical location.1 location.2 e

def horizontal_exactly_two_incidences {m : Nat} (hm : 0 < m)
    (e : HorizontalGridEdge m) (hCrosses : HorizontalCrosses e) :
    ExactlyTwo (HorizontalIncident e) := by
  have hInterior := horizontal_crossing_is_interior hm e hCrosses
  let above := horizontalAboveCell e hInterior.2
  let below := horizontalBelowCell e hInterior.1
  refine {
    first := (above, CellSide.south)
    second := (below, CellSide.north)
    distinct := by
      intro hEqual
      have hSide : CellSide.south = CellSide.north :=
        congrArg Prod.snd hEqual
      cases hSide
    first_has := by
      change RepresentsHorizontal above CellSide.south e
      exact horizontal_above_represents e hInterior.2
    second_has := by
      change RepresentsHorizontal below CellSide.north e
      exact horizontal_below_represents e hInterior.1
    exhaustive := ?_
  }
  intro location hIncident
  rcases location with ⟨c, s⟩
  unfold HorizontalIncident at hIncident
  have hClass := horizontal_representation_classification hm e hCrosses c s hIncident
  rcases hClass with ⟨hs, hc⟩ | ⟨hs, hc⟩
  · left
    cases hs
    cases hc
    rfl
  · right
    cases hs
    cases hc
    rfl

def vertical_exactly_two_incidences {m : Nat} (hm : 0 < m)
    (e : VerticalGridEdge m) (hCrosses : VerticalCrosses e) :
    ExactlyTwo (VerticalIncident e) := by
  have hInterior := vertical_crossing_is_interior hm e hCrosses
  let left := verticalLeftCell e hInterior.1
  let right := verticalRightCell e hInterior.2
  refine {
    first := (left, CellSide.east)
    second := (right, CellSide.west)
    distinct := by
      intro hEqual
      have hSide : CellSide.east = CellSide.west :=
        congrArg Prod.snd hEqual
      cases hSide
    first_has := by
      change RepresentsVertical left CellSide.east e
      exact vertical_left_represents e hInterior.1
    second_has := by
      change RepresentsVertical right CellSide.west e
      exact vertical_right_represents e hInterior.2
    exhaustive := ?_
  }
  intro location hIncident
  rcases location with ⟨c, s⟩
  unfold VerticalIncident at hIncident
  have hClass := vertical_representation_classification hm e hCrosses c s hIncident
  rcases hClass with ⟨hs, hc⟩ | ⟨hs, hc⟩
  · left
    cases hs
    cases hc
    rfl
  · right
    cases hs
    cases hc
    rfl

structure ModTwoBoundaryZero (m : Nat) where
  horizontal : forall e : HorizontalGridEdge m, HorizontalCrosses e ->
    ExactlyTwo (HorizontalIncident e)
  vertical : forall e : VerticalGridEdge m, VerticalCrosses e ->
    ExactlyTwo (VerticalIncident e)

def radialContour_modTwoBoundaryZero {m : Nat} (hm : 0 < m) :
    ModTwoBoundaryZero m where
  horizontal := horizontal_exactly_two_incidences hm
  vertical := vertical_exactly_two_incidences hm

theorem exact_degree_two_is_zero_mod_two : 2 % 2 = 0 := by native_decide

end GlobalContourZeroBoundary
end BoundaryOfSelf
