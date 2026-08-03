import RefinedBoundaryPath

namespace BoundaryOfSelf
namespace GeneralBoundaryMesh

def Inside (threshold index : Nat) : Prop :=
  threshold < index

def EdgeCrosses (threshold edge : Nat) : Prop :=
  (Inside threshold edge /\ Not (Inside threshold (edge + 1))) \/
  (Not (Inside threshold edge) /\ Inside threshold (edge + 1))

theorem edgeCrosses_iff (threshold edge : Nat) :
    EdgeCrosses threshold edge <-> edge = threshold := by
  unfold EdgeCrosses Inside
  constructor
  · intro h
    rcases h with hBackwards | hForwards
    · omega
    · omega
  · intro h
    subst edge
    right
    constructor <;> omega

def MeshNode (n : Nat) := Fin (n + 1)

def MeshEdge (n : Nat) := Fin n

def BandNode (n threshold : Nat) : Region (MeshNode n) :=
  fun x => exists edge : MeshEdge n,
    EdgeCrosses threshold edge.val /\
      (x.val = edge.val \/ x.val = edge.val + 1)

def leftBoundaryNode {n threshold : Nat}
    (hThreshold : threshold < n) : MeshNode n :=
  ⟨threshold, by omega⟩

def rightBoundaryNode {n threshold : Nat}
    (hThreshold : threshold < n) : MeshNode n :=
  ⟨threshold + 1, by omega⟩

theorem bandNode_iff_endpoints
    {n threshold : Nat} (hThreshold : threshold < n)
    (x : MeshNode n) :
    BandNode n threshold x <->
      x.val = threshold \/ x.val = threshold + 1 := by
  constructor
  · intro hx
    rcases hx with ⟨edge, hCrosses, hEndpoint⟩
    have hEdge : edge.val = threshold :=
      (edgeCrosses_iff threshold edge.val).mp hCrosses
    rw [hEdge] at hEndpoint
    exact hEndpoint
  · intro hx
    exact ⟨⟨threshold, hThreshold⟩,
      (edgeCrosses_iff threshold threshold).mpr rfl,
      hx⟩

theorem leftBoundaryNode_isBand
    {n threshold : Nat} (hThreshold : threshold < n) :
    BandNode n threshold (leftBoundaryNode hThreshold) := by
  apply (bandNode_iff_endpoints hThreshold _).mpr
  exact Or.inl rfl

theorem rightBoundaryNode_isBand
    {n threshold : Nat} (hThreshold : threshold < n) :
    BandNode n threshold (rightBoundaryNode hThreshold) := by
  apply (bandNode_iff_endpoints hThreshold _).mpr
  exact Or.inr rfl

theorem boundaryNodes_are_distinct
    {n threshold : Nat} (hThreshold : threshold < n) :
    Not (leftBoundaryNode hThreshold = rightBoundaryNode hThreshold) := by
  intro h
  have hVal := congrArg Fin.val h
  simp [leftBoundaryNode, rightBoundaryNode] at hVal

theorem band_index_width_is_one
    {n threshold : Nat} (hThreshold : threshold < n) :
    (rightBoundaryNode hThreshold).val -
      (leftBoundaryNode hThreshold).val = 1 := by
  simp [leftBoundaryNode, rightBoundaryNode]

structure UnitCellWidth where
  denominator : Nat
  positive : 0 < denominator

def UnitCellWidth.value (w : UnitCellWidth) : Rat :=
  Rat.normalize 1 w.denominator (Nat.ne_of_gt w.positive)

def meshWidth (n : Nat) (hPositive : 0 < n) : UnitCellWidth where
  denominator := n
  positive := hPositive

def NoWiderThan (a b : UnitCellWidth) : Prop :=
  b.denominator <= a.denominator

theorem meshWidth_antitone
    {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (hRefines : m <= n) :
    NoWiderThan (meshWidth n hn) (meshWidth m hm) :=
  hRefines

theorem meshWidth_vanishes_on_reciprocal_basis :
    forall (m : Nat) (hm : 0 < m), exists N : Nat,
      0 < N /\ forall n : Nat, N <= n -> forall hn : 0 < n,
        NoWiderThan (meshWidth n hn) (meshWidth m hm) := by
  intro m hm
  exact ⟨m, hm, by
    intro n hmn hn
    exact meshWidth_antitone hm hn hmn⟩

theorem every_mesh_band_has_one_cell
    {n threshold : Nat} (hThreshold : threshold < n) :
    BandNode n threshold (leftBoundaryNode hThreshold) /\
      BandNode n threshold (rightBoundaryNode hThreshold) /\
      (rightBoundaryNode hThreshold).val -
        (leftBoundaryNode hThreshold).val = 1 := by
  exact ⟨leftBoundaryNode_isBand hThreshold,
    rightBoundaryNode_isBand hThreshold,
    band_index_width_is_one hThreshold⟩

end GeneralBoundaryMesh
end BoundaryOfSelf

#print axioms BoundaryOfSelf.GeneralBoundaryMesh.edgeCrosses_iff
#print axioms BoundaryOfSelf.GeneralBoundaryMesh.bandNode_iff_endpoints
#print axioms BoundaryOfSelf.GeneralBoundaryMesh.boundaryNodes_are_distinct
#print axioms BoundaryOfSelf.GeneralBoundaryMesh.meshWidth_vanishes_on_reciprocal_basis
#print axioms BoundaryOfSelf.GeneralBoundaryMesh.every_mesh_band_has_one_cell
