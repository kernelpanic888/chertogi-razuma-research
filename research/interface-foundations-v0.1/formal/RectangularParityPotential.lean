import MinimalSeparatingContourOrbit

namespace BoundaryOfSelf
namespace RectangularParityPotential

/-!
IF-BS-20B is a self-contained finite rectangular parity lemma. A Boolean edge
marking with even parity around every cell is the gradient of a Boolean vertex
potential. Therefore every marked edge has endpoints of opposite colour, and
no path composed only of colour-preserving steps can cross it.
-/

def bxor : Bool -> Bool -> Bool
  | false, value => value
  | true, value => !value

theorem bxor_eq_true_iff_ne (left right : Bool) :
    bxor left right = true <-> left ≠ right := by
  cases left <;> cases right <;> decide

theorem bxor_nested_cancel (a b c : Bool) :
    bxor (bxor a b) (bxor a (bxor b c)) = c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem parity4_solve_third (a b c d : Bool)
    (even : bxor (bxor a b) (bxor c d) = false) :
    c = bxor (bxor a b) d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [bxor] at even ⊢

theorem transport_step_identity
    (base leftPrefix rightPrefix leftEdge rightEdge current next : Bool)
    (current_eq : bxor (bxor base leftPrefix) rightPrefix = current)
    (next_eq : next = bxor (bxor current rightEdge) leftEdge) :
    bxor (bxor base (bxor leftPrefix leftEdge))
      (bxor rightPrefix rightEdge) = next := by
  cases base <;> cases leftPrefix <;> cases rightPrefix <;>
  cases leftEdge <;> cases rightEdge <;> cases current <;> cases next <;>
    simp [bxor] at current_eq next_eq ⊢

theorem horizontal_gradient_identity
    (base bottomEdge leftVertical rightVertical edge : Bool)
    (transport : bxor (bxor bottomEdge leftVertical) rightVertical = edge) :
    bxor (bxor base leftVertical)
      (bxor (bxor base bottomEdge) rightVertical) = edge := by
  cases base <;> cases bottomEdge <;> cases leftVertical <;>
  cases rightVertical <;> cases edge <;>
    simp [bxor] at transport ⊢

def prefixParity (mark : Nat -> Bool) : Nat -> Bool
  | 0 => false
  | n + 1 => bxor (prefixParity mark n) (mark n)

structure RectangularEdgeMarking where
  horizontal : Nat -> Nat -> Bool
  vertical : Nat -> Nat -> Bool

def CellEven (marking : RectangularEdgeMarking)
    (x y : Nat) : Prop :=
  bxor
    (bxor (marking.horizontal x y) (marking.vertical (x + 1) y))
    (bxor (marking.horizontal x (y + 1)) (marking.vertical x y)) = false

def ClosedOn (marking : RectangularEdgeMarking) (width height : Nat) : Prop :=
  forall x y, x < width -> y < height -> CellEven marking x y

def bottomPrefix (marking : RectangularEdgeMarking) (x : Nat) : Bool :=
  prefixParity (fun i => marking.horizontal i 0) x

def verticalPrefix (marking : RectangularEdgeMarking)
    (x y : Nat) : Bool :=
  prefixParity (fun j => marking.vertical x j) y

def vertexPotential (marking : RectangularEdgeMarking)
    (x y : Nat) : Bool :=
  bxor (bottomPrefix marking x) (verticalPrefix marking x y)

theorem verticalPotential_gradient (marking : RectangularEdgeMarking)
    (x y : Nat) :
    bxor (vertexPotential marking x y)
      (vertexPotential marking x (y + 1)) = marking.vertical x y := by
  unfold vertexPotential verticalPrefix
  rw [prefixParity]
  exact bxor_nested_cancel
    (bottomPrefix marking x)
    (prefixParity (fun j => marking.vertical x j) y)
    (marking.vertical x y)

theorem cellEven_nextHorizontal (marking : RectangularEdgeMarking)
    (x y : Nat) (even : CellEven marking x y) :
    marking.horizontal x (y + 1) =
      bxor
        (bxor (marking.horizontal x y) (marking.vertical (x + 1) y))
        (marking.vertical x y) := by
  exact parity4_solve_third
    (marking.horizontal x y)
    (marking.vertical (x + 1) y)
    (marking.horizontal x (y + 1))
    (marking.vertical x y) even

theorem horizontalTransport (marking : RectangularEdgeMarking)
    (width height x y : Nat) (closed : ClosedOn marking width height)
    (x_bound : x < width) (y_bound : y <= height) :
    bxor
      (bxor (marking.horizontal x 0) (verticalPrefix marking x y))
      (verticalPrefix marking (x + 1) y) = marking.horizontal x y := by
  induction y with
  | zero =>
      cases value : marking.horizontal x 0 <;>
        simp [verticalPrefix, prefixParity, bxor, value]
  | succ y ih =>
      have y_lt : y < height := by omega
      have current := ih (Nat.le_of_succ_le y_bound)
      have next := cellEven_nextHorizontal marking x y
        (closed x y x_bound y_lt)
      simpa [verticalPrefix, prefixParity] using
        transport_step_identity
          (marking.horizontal x 0)
          (verticalPrefix marking x y)
          (verticalPrefix marking (x + 1) y)
          (marking.vertical x y)
          (marking.vertical (x + 1) y)
          (marking.horizontal x y)
          (marking.horizontal x (y + 1))
          current next

theorem horizontalPotential_gradient (marking : RectangularEdgeMarking)
    (width height x y : Nat) (closed : ClosedOn marking width height)
    (x_bound : x < width) (y_bound : y <= height) :
    bxor (vertexPotential marking x y)
      (vertexPotential marking (x + 1) y) = marking.horizontal x y := by
  have transported := horizontalTransport marking width height x y
    closed x_bound y_bound
  unfold vertexPotential bottomPrefix
  rw [prefixParity]
  simpa [verticalPrefix] using
    horizontal_gradient_identity
      (prefixParity (fun i => marking.horizontal i 0) x)
      (marking.horizontal x 0)
      (prefixParity (fun j => marking.vertical x j) y)
      (prefixParity (fun j => marking.vertical (x + 1) j) y)
      (marking.horizontal x y)
      transported

structure RectangularPotentialWitness
    (marking : RectangularEdgeMarking) (width height : Nat) where
  color : Nat -> Nat -> Bool
  horizontal_gradient : forall x y, x < width -> y <= height ->
    bxor (color x y) (color (x + 1) y) = marking.horizontal x y
  vertical_gradient : forall x y, x <= width -> y < height ->
    bxor (color x y) (color x (y + 1)) = marking.vertical x y

def closedMarking_hasPotential
    (marking : RectangularEdgeMarking) (width height : Nat)
    (closed : ClosedOn marking width height) :
    RectangularPotentialWitness marking width height where
  color := vertexPotential marking
  horizontal_gradient := by
    intro x y x_bound y_bound
    exact horizontalPotential_gradient marking width height x y
      closed x_bound y_bound
  vertical_gradient := by
    intro x y _x_bound _y_bound
    exact verticalPotential_gradient marking x y

inductive RelationReachable {Point : Type}
    (Step : Point -> Point -> Prop) : Point -> Point -> Prop where
  | refl (point : Point) : RelationReachable Step point point
  | edge {left right : Point} (step : Step left right) :
      RelationReachable Step left right
  | trans {left middle right : Point}
      (first : RelationReachable Step left middle)
      (second : RelationReachable Step middle right) :
      RelationReachable Step left right

theorem relationReachable_preserves_color {Point : Type}
    (color : Point -> Bool) (Step : Point -> Point -> Prop)
    (preserves : forall {left right}, Step left right -> color left = color right)
    {left right : Point} (path : RelationReachable Step left right) :
    color left = color right := by
  induction path with
  | refl point => exact rfl
  | edge step => exact preserves step
  | trans first second first_ih second_ih => exact first_ih.trans second_ih

theorem no_color_preserving_path_across {Point : Type}
    (color : Point -> Bool) (Step : Point -> Point -> Prop)
    (preserves : forall {left right}, Step left right -> color left = color right)
    {left right : Point} (different : color left ≠ color right) :
    ¬ RelationReachable Step left right := by
  intro path
  exact different (relationReachable_preserves_color color Step preserves path)

theorem marked_horizontal_endpoints_differ
    {marking : RectangularEdgeMarking} {width height x y : Nat}
    (witness : RectangularPotentialWitness marking width height)
    (x_bound : x < width) (y_bound : y <= height)
    (marked : marking.horizontal x y = true) :
    witness.color x y ≠ witness.color (x + 1) y := by
  exact (bxor_eq_true_iff_ne _ _).mp
    ((witness.horizontal_gradient x y x_bound y_bound).trans marked)

theorem marked_vertical_endpoints_differ
    {marking : RectangularEdgeMarking} {width height x y : Nat}
    (witness : RectangularPotentialWitness marking width height)
    (x_bound : x <= width) (y_bound : y < height)
    (marked : marking.vertical x y = true) :
    witness.color x y ≠ witness.color x (y + 1) := by
  exact (bxor_eq_true_iff_ne _ _).mp
    ((witness.vertical_gradient x y x_bound y_bound).trans marked)

end RectangularParityPotential
end BoundaryOfSelf

#print axioms BoundaryOfSelf.RectangularParityPotential.horizontalTransport
#print axioms BoundaryOfSelf.RectangularParityPotential.horizontalPotential_gradient
#print axioms BoundaryOfSelf.RectangularParityPotential.closedMarking_hasPotential
#print axioms BoundaryOfSelf.RectangularParityPotential.relationReachable_preserves_color
#print axioms BoundaryOfSelf.RectangularParityPotential.marked_horizontal_endpoints_differ
#print axioms BoundaryOfSelf.RectangularParityPotential.marked_vertical_endpoints_differ
