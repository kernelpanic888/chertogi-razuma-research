import ConcreteRadialContourTraversal

namespace BoundaryOfSelf
namespace RadialOrthogonalConvexity

open UniformRadialBoundaryFamily
open RefinedCurvedBoundaryGrid

/-!
IF-BS-16 proves the arithmetic connectivity carrier for the sampled radial
inside region. The radial numerator is monotone in both coordinate offsets;
therefore every horizontal and vertical slice of the inside region is an
integer interval. Every inside sample has a certified two-segment orthogonal
connection to the centre which remains inside at every intermediate sample.
-/

def BetweenNat (left middle right : Nat) : Prop :=
  (left <= middle /\ middle <= right) \/
  (right <= middle /\ middle <= left)

theorem betweenNat_refl_left (left right : Nat) :
    BetweenNat left left right := by
  unfold BetweenNat
  omega

theorem betweenNat_refl_right (left right : Nat) :
    BetweenNat left right right := by
  unfold BetweenNat
  omega

theorem betweenNat_symm {left middle right : Nat}
    (h : BetweenNat left middle right) :
    BetweenNat right middle left := by
  unfold BetweenNat at h ⊢
  rcases h with hForward | hBackward
  · exact Or.inr hForward
  · exact Or.inl hBackward

theorem natDistance_between_le_endpoint {left middle right center : Nat}
    (hBetween : BetweenNat left middle right) :
    natDistance middle center <= natDistance left center \/
    natDistance middle center <= natDistance right center := by
  unfold BetweenNat at hBetween
  unfold natDistance
  split <;> split <;> split <;> omega

theorem radialNumerator_le_of_offsets_le {m : Nat}
    (near far : GridSample m)
    (hx : xOffset near <= xOffset far)
    (hy : yOffset near <= yOffset far) :
    radialNumerator near <= radialNumerator far := by
  unfold radialNumerator
  exact Nat.add_le_add (Nat.mul_le_mul hx hx) (Nat.mul_le_mul hy hy)

theorem inside_of_offsets_le {m : Nat} (near far : GridSample m)
    (hx : xOffset near <= xOffset far)
    (hy : yOffset near <= yOffset far)
    (hFarInside : Inside far) : Inside near := by
  unfold Inside at hFarInside ⊢
  exact Nat.le_trans (radialNumerator_le_of_offsets_le near far hx hy)
    hFarInside

theorem outside_of_offsets_ge {m : Nat} (near far : GridSample m)
    (hx : xOffset near <= xOffset far)
    (hy : yOffset near <= yOffset far)
    (hNearOutside : ¬ Inside near) : ¬ Inside far := by
  intro hFarInside
  exact hNearOutside (inside_of_offsets_le near far hx hy hFarInside)

theorem xOffset_eq_of_x {m : Nat} {p q : GridSample m}
    (h : p.x = q.x) : xOffset p = xOffset q := by
  simp [xOffset, h]

theorem yOffset_eq_of_y {m : Nat} {p q : GridSample m}
    (h : p.y = q.y) : yOffset p = yOffset q := by
  simp [yOffset, h]

theorem row_inside_interval {m : Nat}
    (left right middle : GridSample m)
    (hRow : left.y = right.y)
    (hMiddleRow : middle.y = left.y)
    (hBetween : BetweenNat left.x middle.x right.x)
    (hLeftInside : Inside left) (hRightInside : Inside right) :
    Inside middle := by
  rcases natDistance_between_le_endpoint
      (center := centerCoordinate m) hBetween with hNearLeft | hNearRight
  · apply inside_of_offsets_le middle left
    · exact hNearLeft
    · have hY := yOffset_eq_of_y hMiddleRow
      omega
    · exact hLeftInside
  · apply inside_of_offsets_le middle right
    · exact hNearRight
    · have hY := yOffset_eq_of_y (hMiddleRow.trans hRow)
      omega
    · exact hRightInside

theorem column_inside_interval {m : Nat}
    (bottom top middle : GridSample m)
    (hColumn : bottom.x = top.x)
    (hMiddleColumn : middle.x = bottom.x)
    (hBetween : BetweenNat bottom.y middle.y top.y)
    (hBottomInside : Inside bottom) (hTopInside : Inside top) :
    Inside middle := by
  rcases natDistance_between_le_endpoint
      (center := centerCoordinate m) hBetween with hNearBottom | hNearTop
  · apply inside_of_offsets_le middle bottom
    · have hX := xOffset_eq_of_x hMiddleColumn
      omega
    · exact hNearBottom
    · exact hBottomInside
  · apply inside_of_offsets_le middle top
    · have hX := xOffset_eq_of_x (hMiddleColumn.trans hColumn)
      omega
    · exact hNearTop
    · exact hTopInside

def centerSample (m : Nat) : GridSample m where
  x := centerCoordinate m
  y := centerCoordinate m
  x_le := by unfold centerCoordinate; omega
  y_le := by unfold centerCoordinate; omega

theorem centerSample_inside (m : Nat) : Inside (centerSample m) := by
  simp [Inside, centerSample, radialNumerator, xOffset, yOffset,
    centerCoordinate, natDistance, thresholdNumerator]

def rowCenter {m : Nat} (p : GridSample m) : GridSample m where
  x := centerCoordinate m
  y := p.y
  x_le := by unfold centerCoordinate; omega
  y_le := p.y_le

def columnCenter {m : Nat} (p : GridSample m) : GridSample m where
  x := p.x
  y := centerCoordinate m
  x_le := p.x_le
  y_le := by unfold centerCoordinate; omega

theorem rowCenter_inside_of_inside {m : Nat} (p : GridSample m)
    (hInside : Inside p) : Inside (rowCenter p) := by
  apply inside_of_offsets_le (rowCenter p) p
  · simp [rowCenter, xOffset, centerCoordinate, natDistance]
  · have hY := yOffset_eq_of_y (p := rowCenter p) (q := p)
        (by simp [rowCenter])
    omega
  · exact hInside

theorem columnCenter_inside_of_inside {m : Nat} (p : GridSample m)
    (hInside : Inside p) : Inside (columnCenter p) := by
  apply inside_of_offsets_le (columnCenter p) p
  · have hX := xOffset_eq_of_x (p := columnCenter p) (q := p)
        (by simp [columnCenter])
    omega
  · simp [columnCenter, yOffset, centerCoordinate, natDistance]
  · exact hInside

def HorizontalSegmentInside {m : Nat}
    (left right : GridSample m) : Prop :=
  left.y = right.y /\
  forall middle : GridSample m, middle.y = left.y ->
    BetweenNat left.x middle.x right.x -> Inside middle

def VerticalSegmentInside {m : Nat}
    (bottom top : GridSample m) : Prop :=
  bottom.x = top.x /\
  forall middle : GridSample m, middle.x = bottom.x ->
    BetweenNat bottom.y middle.y top.y -> Inside middle

theorem horizontalSegment_inside_of_endpoints {m : Nat}
    (left right : GridSample m) (hRow : left.y = right.y)
    (hLeftInside : Inside left) (hRightInside : Inside right) :
    HorizontalSegmentInside left right := by
  refine ⟨hRow, ?_⟩
  intro middle hMiddleRow hBetween
  exact row_inside_interval left right middle hRow hMiddleRow hBetween
    hLeftInside hRightInside

theorem verticalSegment_inside_of_endpoints {m : Nat}
    (bottom top : GridSample m) (hColumn : bottom.x = top.x)
    (hBottomInside : Inside bottom) (hTopInside : Inside top) :
    VerticalSegmentInside bottom top := by
  refine ⟨hColumn, ?_⟩
  intro middle hMiddleColumn hBetween
  exact column_inside_interval bottom top middle hColumn hMiddleColumn hBetween
    hBottomInside hTopInside

structure InsideLPathToCenter {m : Nat} (start : GridSample m) where
  corner : GridSample m
  horizontal : HorizontalSegmentInside start corner
  vertical : VerticalSegmentInside corner (centerSample m)

def inside_L_path_to_center {m : Nat} (start : GridSample m)
    (hInside : Inside start) : InsideLPathToCenter start where
  corner := rowCenter start
  horizontal := horizontalSegment_inside_of_endpoints start (rowCenter start)
    (by simp [rowCenter]) hInside (rowCenter_inside_of_inside start hInside)
  vertical := verticalSegment_inside_of_endpoints (rowCenter start)
    (centerSample m) (by simp [rowCenter, centerSample])
    (rowCenter_inside_of_inside start hInside) (centerSample_inside m)

theorem radial_inside_is_orthogonally_star_connected {m : Nat}
    (start : GridSample m) (hInside : Inside start) :
    exists corner : GridSample m,
      HorizontalSegmentInside start corner /\
      VerticalSegmentInside corner (centerSample m) := by
  let path := inside_L_path_to_center start hInside
  exact ⟨path.corner, path.horizontal, path.vertical⟩

end RadialOrthogonalConvexity
end BoundaryOfSelf
