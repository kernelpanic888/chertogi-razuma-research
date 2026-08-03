import BoundaryOfSelf

namespace BoundaryOfSelf
namespace FiniteChamber

universe u

def indiscreteClosure {X : Type u} (A : Region X) : Region X :=
  fun _ => exists y, A y

def indiscreteTopology (X : Type u) : ClosureTopology X where
  closure := indiscreteClosure
  subset_closure := by
    intro A x hx
    exact ⟨x, hx⟩
  closure_mono := by
    intro A B hAB x hx
    rcases hx with ⟨y, hy⟩
    exact ⟨y, hAB y hy⟩
  closure_idempotent := by
    intro A
    funext x
    apply propext
    constructor
    · intro h
      rcases h with ⟨_, y, hy⟩
      exact ⟨y, hy⟩
    · intro h
      exact ⟨x, h⟩
  closure_empty := by
    funext x
    apply propext
    constructor
    · intro h
      rcases h with ⟨_, hFalse⟩
      exact hFalse
    · intro hFalse
      exact False.elim hFalse
  closure_union := by
    intro A B
    funext x
    apply propext
    constructor
    · intro h
      rcases h with ⟨y, hyA | hyB⟩
      · exact Or.inl ⟨y, hyA⟩
      · exact Or.inr ⟨y, hyB⟩
    · intro h
      rcases h with hA | hB
      · rcases hA with ⟨y, hy⟩
        exact ⟨y, Or.inl hy⟩
      · rcases hB with ⟨y, hy⟩
        exact ⟨y, Or.inr hy⟩

theorem indiscrete_isConnected {X : Type u} :
    IsConnected (indiscreteTopology X) := by
  intro A hClosed _hOpen
  by_cases hA : exists x, A x
  · right
    intro x
    exact hClosed x hA
  · left
    intro x hx
    exact hA ⟨x, hx⟩

def twoPointD (a b : Bool) : Nat :=
  if a = b then 0 else 2

def chamberRegion : Region Bool :=
  ResolutionRegion twoPointD 1 false

theorem chamber_self_distance :
    twoPointD false false = 0 := by
  decide

theorem chamber_above_threshold :
    exists b, 1 < twoPointD false b := by
  exact ⟨true, by decide⟩

theorem chamberRegion_at_reference :
    Not (chamberRegion false) := by
  simp [chamberRegion, ResolutionRegion, twoPointD]

theorem chamberRegion_at_witness :
    chamberRegion true := by
  simp [chamberRegion, ResolutionRegion, twoPointD]

theorem chamberRegion_isProper :
    ProperRegion chamberRegion :=
  resolutionRegion_isProper twoPointD 1 false
    chamber_self_distance chamber_above_threshold

theorem chamberRegion_hasBoundary :
    BoundaryNonempty (indiscreteTopology Bool) chamberRegion :=
  properRegion_hasTopologicalBoundary
    (indiscreteTopology Bool)
    indiscrete_isConnected
    chamberRegion
    chamberRegion_isProper

def adjacent (x y : Bool) : Prop :=
  x != y

def PlanckTouchBand (A : Region Bool) : Region Bool :=
  fun x => exists y, adjacent x y /\ (A x <-> Not (A y))

theorem frontier_at_reference :
    Frontier (indiscreteTopology Bool) chamberRegion false := by
  exact ⟨⟨true, chamberRegion_at_witness⟩,
    ⟨false, chamberRegion_at_reference⟩⟩

theorem frontier_at_witness :
    Frontier (indiscreteTopology Bool) chamberRegion true := by
  exact ⟨⟨true, chamberRegion_at_witness⟩,
    ⟨false, chamberRegion_at_reference⟩⟩

theorem planckTouch_at_reference :
    PlanckTouchBand chamberRegion false := by
  refine ⟨true, by simp [adjacent], ?_⟩
  constructor
  · intro hInside
    exact False.elim (chamberRegion_at_reference hInside)
  · intro hOutside
    exact False.elim (hOutside chamberRegion_at_witness)

theorem planckTouch_at_witness :
    PlanckTouchBand chamberRegion true := by
  refine ⟨false, by simp [adjacent], ?_⟩
  constructor
  · intro _hInside
    exact chamberRegion_at_reference
  · intro _hOutside
    exact chamberRegion_at_witness

theorem frontier_eq_planckTouchBand :
    Frontier (indiscreteTopology Bool) chamberRegion =
      PlanckTouchBand chamberRegion := by
  funext x
  apply propext
  cases x
  · exact ⟨fun _ => planckTouch_at_reference,
      fun _ => frontier_at_reference⟩
  · exact ⟨fun _ => planckTouch_at_witness,
      fun _ => frontier_at_witness⟩

end FiniteChamber
end BoundaryOfSelf

#print axioms BoundaryOfSelf.FiniteChamber.indiscrete_isConnected
#print axioms BoundaryOfSelf.FiniteChamber.chamberRegion_isProper
#print axioms BoundaryOfSelf.FiniteChamber.chamberRegion_hasBoundary
#print axioms BoundaryOfSelf.FiniteChamber.frontier_eq_planckTouchBand
