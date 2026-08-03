import RadialExteriorConnectivity

namespace BoundaryOfSelf
namespace FiniteGridReachability

open UniformRadialBoundaryFamily
open InterpolatedBoundaryContour
open GlobalContourZeroBoundary
open RadialOrthogonalConvexity
open RadialExteriorConnectivity

/-!
IF-BS-18 turns the integer segment certificates of IF-BS-16/17 into actual
finite paths in the unit-adjacency graph. Every edge preserves the selected
predicate, so the resulting reachability statements are literal connectedness
certificates for the sampled inside and outside subgraphs.
-/

inductive GridReachable {m : Nat} (P : GridSample m -> Prop) :
    GridSample m -> GridSample m -> Prop where
  | refl (point : GridSample m) (has : P point) :
      GridReachable P point point
  | edge (left right : GridSample m)
      (left_has : P left) (right_has : P right)
      (adjacent : UnitAdjacent left right) :
      GridReachable P left right
  | trans (left middle right : GridSample m)
      (first : GridReachable P left middle)
      (second : GridReachable P middle right) :
      GridReachable P left right

theorem gridReachable_symm {m : Nat} {P : GridSample m -> Prop}
    {left right : GridSample m} (h : GridReachable P left right) :
    GridReachable P right left := by
  induction h with
  | refl point has =>
      exact GridReachable.refl point has
  | edge left right left_has right_has adjacent =>
      exact GridReachable.edge right left right_has left_has
        (unitAdjacent_comm adjacent)
  | trans left middle right first second first_ih second_ih =>
      exact GridReachable.trans right middle left second_ih first_ih

theorem horizontal_forward_reachable_aux {m : Nat}
    {P : GridSample m -> Prop} (fuel : Nat)
    (left right : GridSample m)
    (hRow : left.y = right.y)
    (hOrder : left.x <= right.x)
    (hGap : right.x - left.x <= fuel)
    (hSegment : forall middle : GridSample m, middle.y = left.y ->
      BetweenNat left.x middle.x right.x -> P middle) :
    GridReachable P left right := by
  induction fuel generalizing left with
  | zero =>
      have hx : left.x = right.x := by omega
      have hEqual : left = right := gridSample_eq_of_coordinates hx hRow
      subst right
      exact GridReachable.refl left
        (hSegment left rfl (betweenNat_refl_left left.x left.x))
  | succ fuel ih =>
      by_cases hx : left.x = right.x
      · have hEqual : left = right := gridSample_eq_of_coordinates hx hRow
        subst right
        exact GridReachable.refl left
          (hSegment left rfl (betweenNat_refl_left left.x left.x))
      · have hStrict : left.x < right.x := by omega
        let next : GridSample m := {
          x := left.x + 1
          y := left.y
          x_le := by have h := right.x_le; omega
          y_le := left.y_le
        }
        have hNextOrder : next.x <= right.x := by
          dsimp [next]
          omega
        have hNextGap : right.x - next.x <= fuel := by
          dsimp [next]
          omega
        have hLeftHas : P left :=
          hSegment left rfl (betweenNat_refl_left left.x right.x)
        have hNextBetween : BetweenNat left.x next.x right.x := by
          unfold BetweenNat
          dsimp [next]
          omega
        have hNextHas : P next := hSegment next rfl hNextBetween
        have hAdjacent : UnitAdjacent left next := by
          unfold UnitAdjacent
          left
          exact ⟨rfl, Or.inl rfl⟩
        have hTailSegment : forall middle : GridSample m,
            middle.y = next.y ->
            BetweenNat next.x middle.x right.x -> P middle := by
          intro middle hMiddleRow hBetween
          apply hSegment middle
          · simpa [next] using hMiddleRow
          · unfold BetweenNat at hBetween ⊢
            dsimp [next] at hBetween ⊢
            omega
        have hTail : GridReachable P next right :=
          ih next (by simpa [next] using hRow) hNextOrder hNextGap
            hTailSegment
        exact GridReachable.trans left next right
          (GridReachable.edge left next hLeftHas hNextHas hAdjacent) hTail

theorem horizontal_segment_reachable {m : Nat}
    {P : GridSample m -> Prop} (left right : GridSample m)
    (hRow : left.y = right.y)
    (hSegment : forall middle : GridSample m, middle.y = left.y ->
      BetweenNat left.x middle.x right.x -> P middle) :
    GridReachable P left right := by
  by_cases hOrder : left.x <= right.x
  · exact horizontal_forward_reachable_aux (right.x - left.x)
      left right hRow hOrder (Nat.le_refl _) hSegment
  · have hReverseSegment : forall middle : GridSample m,
        middle.y = right.y ->
        BetweenNat right.x middle.x left.x -> P middle := by
      intro middle hMiddleRow hBetween
      apply hSegment middle
      · exact hMiddleRow.trans hRow.symm
      · exact betweenNat_symm hBetween
    have hForward : GridReachable P right left :=
      horizontal_forward_reachable_aux (left.x - right.x)
        right left hRow.symm (by omega) (Nat.le_refl _) hReverseSegment
    exact gridReachable_symm hForward

theorem vertical_forward_reachable_aux {m : Nat}
    {P : GridSample m -> Prop} (fuel : Nat)
    (bottom top : GridSample m)
    (hColumn : bottom.x = top.x)
    (hOrder : bottom.y <= top.y)
    (hGap : top.y - bottom.y <= fuel)
    (hSegment : forall middle : GridSample m, middle.x = bottom.x ->
      BetweenNat bottom.y middle.y top.y -> P middle) :
    GridReachable P bottom top := by
  induction fuel generalizing bottom with
  | zero =>
      have hy : bottom.y = top.y := by omega
      have hEqual : bottom = top := gridSample_eq_of_coordinates hColumn hy
      subst top
      exact GridReachable.refl bottom
        (hSegment bottom rfl (betweenNat_refl_left bottom.y bottom.y))
  | succ fuel ih =>
      by_cases hy : bottom.y = top.y
      · have hEqual : bottom = top := gridSample_eq_of_coordinates hColumn hy
        subst top
        exact GridReachable.refl bottom
          (hSegment bottom rfl (betweenNat_refl_left bottom.y bottom.y))
      · have hStrict : bottom.y < top.y := by omega
        let next : GridSample m := {
          x := bottom.x
          y := bottom.y + 1
          x_le := bottom.x_le
          y_le := by have h := top.y_le; omega
        }
        have hNextOrder : next.y <= top.y := by
          dsimp [next]
          omega
        have hNextGap : top.y - next.y <= fuel := by
          dsimp [next]
          omega
        have hBottomHas : P bottom :=
          hSegment bottom rfl (betweenNat_refl_left bottom.y top.y)
        have hNextBetween : BetweenNat bottom.y next.y top.y := by
          unfold BetweenNat
          dsimp [next]
          omega
        have hNextHas : P next := hSegment next rfl hNextBetween
        have hAdjacent : UnitAdjacent bottom next := by
          unfold UnitAdjacent
          right
          exact ⟨rfl, Or.inl rfl⟩
        have hTailSegment : forall middle : GridSample m,
            middle.x = next.x ->
            BetweenNat next.y middle.y top.y -> P middle := by
          intro middle hMiddleColumn hBetween
          apply hSegment middle
          · simpa [next] using hMiddleColumn
          · unfold BetweenNat at hBetween ⊢
            dsimp [next] at hBetween ⊢
            omega
        have hTail : GridReachable P next top :=
          ih next (by simpa [next] using hColumn) hNextOrder hNextGap
            hTailSegment
        exact GridReachable.trans bottom next top
          (GridReachable.edge bottom next hBottomHas hNextHas hAdjacent) hTail

theorem vertical_segment_reachable {m : Nat}
    {P : GridSample m -> Prop} (bottom top : GridSample m)
    (hColumn : bottom.x = top.x)
    (hSegment : forall middle : GridSample m, middle.x = bottom.x ->
      BetweenNat bottom.y middle.y top.y -> P middle) :
    GridReachable P bottom top := by
  by_cases hOrder : bottom.y <= top.y
  · exact vertical_forward_reachable_aux (top.y - bottom.y)
      bottom top hColumn hOrder (Nat.le_refl _) hSegment
  · have hReverseSegment : forall middle : GridSample m,
        middle.x = top.x ->
        BetweenNat top.y middle.y bottom.y -> P middle := by
      intro middle hMiddleColumn hBetween
      apply hSegment middle
      · exact hMiddleColumn.trans hColumn.symm
      · exact betweenNat_symm hBetween
    have hForward : GridReachable P top bottom :=
      vertical_forward_reachable_aux (bottom.y - top.y)
        top bottom hColumn.symm (by omega) (Nat.le_refl _) hReverseSegment
    exact gridReachable_symm hForward

theorem horizontalInside_reachable {m : Nat}
    {left right : GridSample m}
    (h : HorizontalSegmentInside left right) :
    GridReachable Inside left right := by
  exact horizontal_segment_reachable left right h.1 h.2

theorem verticalInside_reachable {m : Nat}
    {bottom top : GridSample m}
    (h : VerticalSegmentInside bottom top) :
    GridReachable Inside bottom top := by
  exact vertical_segment_reachable bottom top h.1 h.2

theorem horizontalOutside_reachable {m : Nat}
    {left right : GridSample m}
    (h : HorizontalSegmentOutside left right) :
    GridReachable (fun point => ¬ Inside point) left right := by
  exact horizontal_segment_reachable left right h.1 h.2

theorem verticalOutside_reachable {m : Nat}
    {bottom top : GridSample m}
    (h : VerticalSegmentOutside bottom top) :
    GridReachable (fun point => ¬ Inside point) bottom top := by
  exact vertical_segment_reachable bottom top h.1 h.2

theorem every_inside_sample_reaches_center {m : Nat}
    (start : GridSample m) (hInside : Inside start) :
    GridReachable Inside start (centerSample m) := by
  let path := inside_L_path_to_center start hInside
  exact GridReachable.trans start path.corner (centerSample m)
    (horizontalInside_reachable path.horizontal)
    (verticalInside_reachable path.vertical)

theorem every_outside_sample_reaches_frame_corner {m : Nat}
    (hm : 0 < m) (start : GridSample m) (hOutside : ¬ Inside start) :
    GridReachable (fun point => ¬ Inside point)
      start (originFrameCorner m) := by
  let path := outside_path_to_frame_corner hm start hOutside
  exact GridReachable.trans start path.xFrame (originFrameCorner m)
    (horizontalOutside_reachable path.first)
    (GridReachable.trans path.xFrame path.bottomFrame (originFrameCorner m)
      (verticalOutside_reachable path.second)
      (horizontalOutside_reachable path.third))

theorem any_two_inside_samples_connected {m : Nat}
    (left right : GridSample m) (hLeft : Inside left) (hRight : Inside right) :
    GridReachable Inside left right := by
  exact GridReachable.trans left (centerSample m) right
    (every_inside_sample_reaches_center left hLeft)
    (gridReachable_symm (every_inside_sample_reaches_center right hRight))

theorem any_two_outside_samples_connected {m : Nat} (hm : 0 < m)
    (left right : GridSample m) (hLeft : ¬ Inside left)
    (hRight : ¬ Inside right) :
    GridReachable (fun point => ¬ Inside point) left right := by
  exact GridReachable.trans left (originFrameCorner m) right
    (every_outside_sample_reaches_frame_corner hm left hLeft)
    (gridReachable_symm
      (every_outside_sample_reaches_frame_corner hm right hRight))

end FiniteGridReachability
end BoundaryOfSelf
