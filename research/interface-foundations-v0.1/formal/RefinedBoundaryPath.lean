import FiniteBoundaryChamber

namespace BoundaryOfSelf
namespace RefinedBoundaryPath

inductive CoarseNode where
  | c0
  | c1
  | c2
deriving DecidableEq, Repr

inductive FineNode where
  | f0
  | f1
  | f2
  | f3
  | f4
deriving DecidableEq, Repr

def coarseD : CoarseNode -> Nat
  | .c0 => 0
  | .c1 => 2
  | .c2 => 4

def fineD : FineNode -> Nat
  | .f0 => 0
  | .f1 => 1
  | .f2 => 2
  | .f3 => 3
  | .f4 => 4

def coarseInside : CoarseNode -> Bool
  | .c0 => false
  | .c1 => false
  | .c2 => true

def fineInside : FineNode -> Bool
  | .f0 => false
  | .f1 => false
  | .f2 => false
  | .f3 => true
  | .f4 => true

theorem coarseInside_iff_threshold (x : CoarseNode) :
    coarseInside x = true <-> 2 < coarseD x := by
  cases x <;> decide

theorem fineInside_iff_threshold (x : FineNode) :
    fineInside x = true <-> 2 < fineD x := by
  cases x <;> decide

def crosses {X : Type} (inside : X -> Bool) (x y : X) : Bool :=
  Bool.xor (inside x) (inside y)

def coarseBandFlag : CoarseNode -> Bool
  | .c0 => crosses coarseInside .c0 .c1
  | .c1 => crosses coarseInside .c0 .c1 ||
      crosses coarseInside .c1 .c2
  | .c2 => crosses coarseInside .c1 .c2

def fineBandFlag : FineNode -> Bool
  | .f0 => crosses fineInside .f0 .f1
  | .f1 => crosses fineInside .f0 .f1 ||
      crosses fineInside .f1 .f2
  | .f2 => crosses fineInside .f1 .f2 ||
      crosses fineInside .f2 .f3
  | .f3 => crosses fineInside .f2 .f3 ||
      crosses fineInside .f3 .f4
  | .f4 => crosses fineInside .f3 .f4

def CoarseBand : Region CoarseNode :=
  fun x => coarseBandFlag x = true

def FineBand : Region FineNode :=
  fun x => fineBandFlag x = true

theorem coarse_band_profile :
    Not (CoarseBand .c0) /\ CoarseBand .c1 /\ CoarseBand .c2 := by
  simp [CoarseBand, coarseBandFlag, crosses, coarseInside]

theorem fine_band_profile :
    Not (FineBand .f0) /\ Not (FineBand .f1) /\
      FineBand .f2 /\ FineBand .f3 /\ Not (FineBand .f4) := by
  simp [FineBand, fineBandFlag, crosses, fineInside]

def coarsen : FineNode -> CoarseNode
  | .f0 => .c0
  | .f1 => .c0
  | .f2 => .c1
  | .f3 => .c2
  | .f4 => .c2

theorem fineBand_maps_to_coarseBand
    (x : FineNode) (hx : FineBand x) :
    CoarseBand (coarsen x) := by
  cases x <;>
    simp [FineBand, fineBandFlag, crosses, fineInside,
      CoarseBand, coarseBandFlag, coarseInside, coarsen] at hx ⊢

theorem coarseBand_has_fine_lift
    (x : CoarseNode) (hx : CoarseBand x) :
    exists y, coarsen y = x /\ FineBand y := by
  cases x
  · exact False.elim (coarse_band_profile.1 hx)
  · exact ⟨.f2, rfl, fine_band_profile.2.2.1⟩
  · exact ⟨.f3, rfl, fine_band_profile.2.2.2.1⟩

def CoarsenedFineBand : Region CoarseNode :=
  fun x => exists y, coarsen y = x /\ FineBand y

theorem coarseBand_eq_coarsenedFineBand :
    CoarseBand = CoarsenedFineBand := by
  funext x
  apply propext
  constructor
  · exact coarseBand_has_fine_lift x
  · intro hLift
    rcases hLift with ⟨y, hy, hBand⟩
    rw [← hy]
    exact fineBand_maps_to_coarseBand y hBand

theorem threshold_edge_is_unique_coarse :
    crosses coarseInside .c0 .c1 = false /\
      crosses coarseInside .c1 .c2 = true := by
  simp [crosses, coarseInside]

theorem threshold_edge_is_unique_fine :
    crosses fineInside .f0 .f1 = false /\
      crosses fineInside .f1 .f2 = false /\
      crosses fineInside .f2 .f3 = true /\
      crosses fineInside .f3 .f4 = false := by
  simp [crosses, fineInside]

end RefinedBoundaryPath
end BoundaryOfSelf

#print axioms BoundaryOfSelf.RefinedBoundaryPath.coarseInside_iff_threshold
#print axioms BoundaryOfSelf.RefinedBoundaryPath.fineInside_iff_threshold
#print axioms BoundaryOfSelf.RefinedBoundaryPath.fineBand_maps_to_coarseBand
#print axioms BoundaryOfSelf.RefinedBoundaryPath.coarseBand_has_fine_lift
#print axioms BoundaryOfSelf.RefinedBoundaryPath.coarseBand_eq_coarsenedFineBand
