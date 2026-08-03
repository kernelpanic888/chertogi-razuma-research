import RadialOrthogonalConvexity

namespace BoundaryOfSelf
namespace RadialExteriorConnectivity

open RefinedCurvedBoundaryGrid
open UniformRadialBoundaryFamily
open GlobalContourIncidence
open RadialOrthogonalConvexity

/-!
IF-BS-17 proves the arithmetic connectivity carrier for the sampled radial
exterior. Every outside sample first moves away from the centre to a vertical
outer frame, then follows that frame to the bottom edge, and finally reaches
the common corner `(0,0)`. Every intermediate integer sample remains outside.
-/

def outwardX {m : Nat} (p : GridSample m) : Nat :=
  if p.x <= centerCoordinate m then 0 else 4 * m

theorem outwardX_le {m : Nat} (p : GridSample m) :
    outwardX p <= 4 * m := by
  unfold outwardX
  split <;> omega

theorem outwardX_outer {m : Nat} (p : GridSample m) :
    outwardX p = 0 \/ outwardX p = 4 * m := by
  unfold outwardX
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem xOffset_le_on_outward_segment {m : Nat}
    (start middle : GridSample m)
    (hBetween : BetweenNat start.x middle.x (outwardX start)) :
    xOffset start <= xOffset middle := by
  have hStartBound := start.x_le
  have hMiddleBound := middle.x_le
  unfold outwardX at hBetween
  split at hBetween
  case isTrue hLeft =>
    unfold centerCoordinate at hLeft
    unfold BetweenNat at hBetween
    unfold xOffset centerCoordinate natDistance
    split <;> split <;> omega
  case isFalse hRight =>
    unfold centerCoordinate at hRight
    unfold BetweenNat at hBetween
    unfold xOffset centerCoordinate natDistance
    split <;> split <;> omega

def xFramePoint {m : Nat} (p : GridSample m) : GridSample m where
  x := outwardX p
  y := p.y
  x_le := outwardX_le p
  y_le := p.y_le

def bottomFramePoint {m : Nat} (p : GridSample m) : GridSample m where
  x := outwardX p
  y := 0
  x_le := outwardX_le p
  y_le := by omega

def originFrameCorner (m : Nat) : GridSample m where
  x := 0
  y := 0
  x_le := by omega
  y_le := by omega

def HorizontalSegmentOutside {m : Nat}
    (left right : GridSample m) : Prop :=
  left.y = right.y /\
  forall middle : GridSample m, middle.y = left.y ->
    BetweenNat left.x middle.x right.x -> ¬ Inside middle

def VerticalSegmentOutside {m : Nat}
    (bottom top : GridSample m) : Prop :=
  bottom.x = top.x /\
  forall middle : GridSample m, middle.x = bottom.x ->
    BetweenNat bottom.y middle.y top.y -> ¬ Inside middle

theorem outward_horizontal_segment_outside {m : Nat}
    (start : GridSample m) (hOutside : ¬ Inside start) :
    HorizontalSegmentOutside start (xFramePoint start) := by
  refine ⟨by simp [xFramePoint], ?_⟩
  intro middle hRow hBetween
  apply outside_of_offsets_ge start middle
  · exact xOffset_le_on_outward_segment start middle hBetween
  · have hY := yOffset_eq_of_y hRow
    omega
  · exact hOutside

theorem vertical_outer_frame_segment_outside {m : Nat} (hm : 0 < m)
    (start : GridSample m) :
    VerticalSegmentOutside (xFramePoint start) (bottomFramePoint start) := by
  refine ⟨by simp [xFramePoint, bottomFramePoint], ?_⟩
  intro middle hColumn _
  apply outside_of_x_outer hm middle
  rcases outwardX_outer start with hZero | hMax
  · left
    simpa [xFramePoint, hZero] using hColumn
  · right
    simpa [xFramePoint, hMax] using hColumn

theorem bottom_outer_frame_segment_outside {m : Nat} (hm : 0 < m)
    (start : GridSample m) :
    HorizontalSegmentOutside (bottomFramePoint start) (originFrameCorner m) := by
  refine ⟨by simp [bottomFramePoint, originFrameCorner], ?_⟩
  intro middle hRow _
  apply outside_of_y_outer hm middle
  left
  simpa [bottomFramePoint] using hRow

theorem xFramePoint_outside {m : Nat} (hm : 0 < m)
    (start : GridSample m) : ¬ Inside (xFramePoint start) := by
  apply outside_of_x_outer hm
  rcases outwardX_outer start with hZero | hMax
  · exact Or.inl (by simpa [xFramePoint] using hZero)
  · exact Or.inr (by simpa [xFramePoint] using hMax)

theorem bottomFramePoint_outside {m : Nat} (hm : 0 < m)
    (start : GridSample m) : ¬ Inside (bottomFramePoint start) := by
  apply outside_of_y_outer hm
  exact Or.inl (by simp [bottomFramePoint])

theorem originFrameCorner_outside {m : Nat} (hm : 0 < m) :
    ¬ Inside (originFrameCorner m) := by
  apply outside_of_x_outer hm
  exact Or.inl (by simp [originFrameCorner])

structure OutsidePathToFrameCorner {m : Nat} (start : GridSample m) where
  xFrame : GridSample m
  bottomFrame : GridSample m
  first : HorizontalSegmentOutside start xFrame
  second : VerticalSegmentOutside xFrame bottomFrame
  third : HorizontalSegmentOutside bottomFrame (originFrameCorner m)

def outside_path_to_frame_corner {m : Nat} (hm : 0 < m)
    (start : GridSample m) (hOutside : ¬ Inside start) :
    OutsidePathToFrameCorner start where
  xFrame := xFramePoint start
  bottomFrame := bottomFramePoint start
  first := outward_horizontal_segment_outside start hOutside
  second := vertical_outer_frame_segment_outside hm start
  third := bottom_outer_frame_segment_outside hm start

theorem radial_outside_reaches_common_frame_corner {m : Nat}
    (hm : 0 < m) (start : GridSample m) (hOutside : ¬ Inside start) :
    exists xFrame bottomFrame : GridSample m,
      HorizontalSegmentOutside start xFrame /\
      VerticalSegmentOutside xFrame bottomFrame /\
      HorizontalSegmentOutside bottomFrame (originFrameCorner m) := by
  let path := outside_path_to_frame_corner hm start hOutside
  exact ⟨path.xFrame, path.bottomFrame, path.first, path.second, path.third⟩

end RadialExteriorConnectivity
end BoundaryOfSelf
