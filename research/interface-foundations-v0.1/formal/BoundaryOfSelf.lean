import Std

namespace BoundaryOfSelf

universe u

abbrev Region (X : Type u) := X -> Prop

def Subset {X : Type u} (A B : Region X) : Prop :=
  forall x, A x -> B x

def Complement {X : Type u} (A : Region X) : Region X :=
  fun x => Not (A x)

def Inter {X : Type u} (A B : Region X) : Region X :=
  fun x => A x /\ B x

def Union {X : Type u} (A B : Region X) : Region X :=
  fun x => A x \/ B x

def EmptyRegion {X : Type u} (A : Region X) : Prop :=
  ∀ x, ¬ A x

def WholeRegion {X : Type u} (A : Region X) : Prop :=
  ∀ x, A x

def ProperRegion {X : Type u} (A : Region X) : Prop :=
  (∃ x, A x) ∧ (∃ x, ¬ A x)

def ConnectedBoundaryLaw {X : Type u}
    (Boundary : Region X -> Prop) : Prop :=
  ∀ A, ¬ Boundary A -> EmptyRegion A ∨ WholeRegion A

def SelfRecord {X : Type u}
    (Boundary : Region X -> Prop) (p : X) (A : Region X) : Prop :=
  A p ∧ Boundary A ∧ ∃ q, ¬ A q

/- A minimal concrete topology, presented by the standard Kuratowski closure
   axioms. The boundary theorem below is no longer accepted as an input law. -/
structure ClosureTopology (X : Type u) where
  closure : Region X -> Region X
  subset_closure : forall A, Subset A (closure A)
  closure_mono : forall {A B}, Subset A B -> Subset (closure A) (closure B)
  closure_idempotent : forall A, closure (closure A) = closure A
  closure_empty : closure (fun _ => False) = (fun _ => False)
  closure_union : forall A B,
    closure (Union A B) = Union (closure A) (closure B)

def IsClosed {X : Type u} (T : ClosureTopology X) (A : Region X) : Prop :=
  Subset (T.closure A) A

def IsOpen {X : Type u} (T : ClosureTopology X) (A : Region X) : Prop :=
  IsClosed T (Complement A)

def Interior {X : Type u} (T : ClosureTopology X) (A : Region X) : Region X :=
  Complement (T.closure (Complement A))

def Frontier {X : Type u} (T : ClosureTopology X) (A : Region X) : Region X :=
  Inter (T.closure A) (T.closure (Complement A))

def BoundaryNonempty {X : Type u}
    (T : ClosureTopology X) (A : Region X) : Prop :=
  exists x, Frontier T A x

def IsConnected {X : Type u} (T : ClosureTopology X) : Prop :=
  forall A, IsClosed T A -> IsOpen T A -> EmptyRegion A \/ WholeRegion A

def ResolutionRegion {X : Type u}
    (D : X -> X -> Nat) (eps : Nat) (a : X) : Region X :=
  fun b => eps < D a b

def TopologicalSelfRecord {X : Type u}
    (T : ClosureTopology X) (p : X) (A : Region X) : Prop :=
  Interior T A p /\ exists q, Not (A q)

theorem properRegion_hasBoundary
    {X : Type u} (Boundary : Region X -> Prop)
    (hConnected : ConnectedBoundaryLaw Boundary)
    (A : Region X) (hProper : ProperRegion A) :
    Boundary A := by
  apply Classical.byContradiction
  intro hNoBoundary
  rcases hConnected A hNoBoundary with hEmpty | hWhole
  · rcases hProper.1 with ⟨x, hx⟩
    exact hEmpty x hx
  · rcases hProper.2 with ⟨x, hx⟩
    exact hx (hWhole x)

theorem boundarylessRegion_is_empty_or_whole
    {X : Type u} (Boundary : Region X -> Prop)
    (hConnected : ConnectedBoundaryLaw Boundary)
    (A : Region X) (hNoBoundary : ¬ Boundary A) :
    EmptyRegion A ∨ WholeRegion A :=
  hConnected A hNoBoundary

theorem selfRecord_contains_first_distinction
    {X : Type u} (Boundary : Region X -> Prop)
    (p : X) (A : Region X)
    (hSelf : SelfRecord Boundary p A) :
    ∃ q, A p ∧ ¬ A q := by
  rcases hSelf.2.2 with ⟨q, hOutside⟩
  exact ⟨q, hSelf.1, hOutside⟩

theorem selfRecord_is_proper
    {X : Type u} (Boundary : Region X -> Prop)
    (p : X) (A : Region X)
    (hSelf : SelfRecord Boundary p A) :
    ProperRegion A := by
  refine ⟨⟨p, hSelf.1⟩, ?_⟩
  exact hSelf.2.2

theorem frontier_empty_implies_closed
    {X : Type u} (T : ClosureTopology X) (A : Region X)
    (hEmpty : EmptyRegion (Frontier T A)) :
    IsClosed T A := by
  intro x hxClosure
  apply Classical.byContradiction
  intro hxOutside
  have hxOtherClosure : T.closure (Complement A) x :=
    T.subset_closure (Complement A) x hxOutside
  exact hEmpty x ⟨hxClosure, hxOtherClosure⟩

theorem frontier_empty_implies_open
    {X : Type u} (T : ClosureTopology X) (A : Region X)
    (hEmpty : EmptyRegion (Frontier T A)) :
    IsOpen T A := by
  intro x hxOtherClosure hxInside
  have hxClosure : T.closure A x :=
    T.subset_closure A x hxInside
  exact hEmpty x ⟨hxClosure, hxOtherClosure⟩

theorem boundarylessRegion_is_empty_or_whole_topological
    {X : Type u} (T : ClosureTopology X)
    (hConnected : IsConnected T) (A : Region X)
    (hNoBoundary : Not (BoundaryNonempty T A)) :
    EmptyRegion A \/ WholeRegion A := by
  have hEmpty : EmptyRegion (Frontier T A) := by
    intro x hx
    exact hNoBoundary ⟨x, hx⟩
  exact hConnected A
    (frontier_empty_implies_closed T A hEmpty)
    (frontier_empty_implies_open T A hEmpty)

theorem properRegion_hasTopologicalBoundary
    {X : Type u} (T : ClosureTopology X)
    (hConnected : IsConnected T) (A : Region X)
    (hProper : ProperRegion A) :
    BoundaryNonempty T A := by
  apply Classical.byContradiction
  intro hNoBoundary
  rcases boundarylessRegion_is_empty_or_whole_topological
      T hConnected A hNoBoundary with hEmpty | hWhole
  · rcases hProper.1 with ⟨x, hx⟩
    exact hEmpty x hx
  · rcases hProper.2 with ⟨x, hx⟩
    exact hx (hWhole x)

theorem interior_subset
    {X : Type u} (T : ClosureTopology X) (A : Region X) :
    Subset (Interior T A) A := by
  intro x hxInterior
  apply Classical.byContradiction
  intro hxOutside
  exact hxInterior (T.subset_closure (Complement A) x hxOutside)

theorem topologicalSelf_isProper
    {X : Type u} (T : ClosureTopology X)
    (p : X) (A : Region X)
    (hSelf : TopologicalSelfRecord T p A) :
    ProperRegion A := by
  refine ⟨⟨p, interior_subset T A p hSelf.1⟩, ?_⟩
  exact hSelf.2

theorem topologicalSelf_hasBoundary
    {X : Type u} (T : ClosureTopology X)
    (hConnected : IsConnected T)
    (p : X) (A : Region X)
    (hSelf : TopologicalSelfRecord T p A) :
    BoundaryNonempty T A :=
  properRegion_hasTopologicalBoundary T hConnected A
    (topologicalSelf_isProper T p A hSelf)

theorem resolutionRegion_isProper
    {X : Type u} (D : X -> X -> Nat) (eps : Nat) (a : X)
    (hSelfDistance : D a a = 0)
    (hWitness : exists b, eps < D a b) :
    ProperRegion (ResolutionRegion D eps a) := by
  rcases hWitness with ⟨b, hb⟩
  refine ⟨⟨b, hb⟩, ⟨a, ?_⟩⟩
  show Not (eps < D a a)
  simp [hSelfDistance]

theorem resolutionRegion_hasBoundary
    {X : Type u} (T : ClosureTopology X)
    (hConnected : IsConnected T)
    (D : X -> X -> Nat) (eps : Nat) (a : X)
    (hSelfDistance : D a a = 0)
    (hWitness : exists b, eps < D a b) :
    BoundaryNonempty T (ResolutionRegion D eps a) :=
  properRegion_hasTopologicalBoundary T hConnected
    (ResolutionRegion D eps a)
    (resolutionRegion_isProper D eps a hSelfDistance hWitness)

end BoundaryOfSelf

#print axioms BoundaryOfSelf.properRegion_hasBoundary
#print axioms BoundaryOfSelf.boundarylessRegion_is_empty_or_whole
#print axioms BoundaryOfSelf.selfRecord_contains_first_distinction
#print axioms BoundaryOfSelf.selfRecord_is_proper
#print axioms BoundaryOfSelf.boundarylessRegion_is_empty_or_whole_topological
#print axioms BoundaryOfSelf.properRegion_hasTopologicalBoundary
#print axioms BoundaryOfSelf.topologicalSelf_hasBoundary
#print axioms BoundaryOfSelf.resolutionRegion_isProper
#print axioms BoundaryOfSelf.resolutionRegion_hasBoundary
