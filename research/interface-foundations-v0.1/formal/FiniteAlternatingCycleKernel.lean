import GlobalContourZeroBoundary

namespace BoundaryOfSelf
namespace FiniteAlternatingCycleKernel

/-!
IF-BS-14 supplies the finite combinatorial kernel needed after IF-BS-13.
Two fixed-point-free involutions encode the other endpoint of a local segment
and the other cell at a shared contour vertex. Their alternating composition
is a permutation. A self-contained pigeonhole argument proves that every state
in a finitely enumerated traversal lies on a positive closed orbit.
-/

def iterate {alpha : Type} (f : alpha -> alpha) : Nat -> alpha -> alpha
  | 0, x => x
  | n + 1, x => f (iterate f n x)

theorem iterate_succ_start {alpha : Type} (f : alpha -> alpha)
    (n : Nat) (x : alpha) :
    iterate f n (f x) = iterate f (n + 1) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [iterate, ih]

theorem iterate_add {alpha : Type} (f : alpha -> alpha)
    (a b : Nat) (x : alpha) :
    iterate f (a + b) x = iterate f a (iterate f b x) := by
  induction a with
  | zero => simp [iterate]
  | succ a ih =>
      simp [Nat.succ_add, iterate, ih]

def orbitList {alpha : Type} (f : alpha -> alpha) :
    alpha -> Nat -> List alpha
  | _, 0 => []
  | x, n + 1 => x :: orbitList f (f x) n

theorem orbitList_length {alpha : Type} (f : alpha -> alpha)
    (x : alpha) (n : Nat) :
    (orbitList f x n).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp [orbitList, ih]

theorem mem_orbitList_iff {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    (f : alpha -> alpha) (x y : alpha) (n : Nat) :
    y ∈ orbitList f x n <->
      exists k : Nat, k < n /\ iterate f k x = y := by
  induction n generalizing x with
  | zero => simp [orbitList]
  | succ n ih =>
      constructor
      · intro hMem
        simp only [orbitList, List.mem_cons] at hMem
        rcases hMem with hHead | hTail
        · refine ⟨0, by omega, ?_⟩
          simpa [iterate] using hHead.symm
        · rcases (ih (f x)).mp hTail with ⟨k, hk, hValue⟩
          refine ⟨k + 1, by omega, ?_⟩
          rw [← iterate_succ_start]
          exact hValue
      · rintro ⟨k, hk, hValue⟩
        by_cases hkZero : k = 0
        · subst k
          simp [orbitList, iterate] at hValue ⊢
          exact Or.inl hValue.symm
        · have hkPos : 0 < k := by omega
          let predecessorIndex := k - 1
          have hkShape : predecessorIndex + 1 = k := by
            dsimp [predecessorIndex]
            omega
          have hkBound : predecessorIndex < n := by
            dsimp [predecessorIndex]
            omega
          have hTailValue : iterate f predecessorIndex (f x) = y := by
            rw [iterate_succ_start, hkShape]
            exact hValue
          simp only [orbitList, List.mem_cons]
          exact Or.inr ((ih (f x)).mpr ⟨predecessorIndex, hkBound, hTailValue⟩)

theorem nodup_length_le_of_cover {alpha : Type} [BEq alpha]
    [LawfulBEq alpha] (values cover : List alpha)
    (hNodup : values.Nodup)
    (hCover : forall x, x ∈ values -> x ∈ cover) :
    values.length <= cover.length := by
  induction values generalizing cover with
  | nil => simp
  | cons a tail ih =>
      have hParts := List.nodup_cons.mp hNodup
      have haCover : a ∈ cover :=
        hCover a (List.mem_cons.mpr (Or.inl rfl))
      have hTailCover : forall x, x ∈ tail -> x ∈ cover.erase a := by
        intro x hx
        have hxa : x ≠ a := by
          intro hEqual
          subst x
          exact hParts.1 hx
        apply (List.mem_erase_of_ne hxa).mpr
        exact hCover x (List.mem_cons.mpr (Or.inr hx))
      have hTailLength := ih (cover.erase a) hParts.2 hTailCover
      have hEraseLength := List.length_erase_of_mem haCover
      have hCoverPos : 0 < cover.length := by
        cases cover with
        | nil => simp at haCover
        | cons head rest => simp
      simp only [List.length_cons]
      omega

theorem orbit_not_nodup_has_repeat {alpha : Type} [BEq alpha]
    [LawfulBEq alpha] (f : alpha -> alpha) (x : alpha) (n : Nat)
    (hNotNodup : ¬ (orbitList f x n).Nodup) :
    exists i j : Nat,
      i < j /\ j < n /\ iterate f i x = iterate f j x := by
  induction n generalizing x with
  | zero =>
      simp [orbitList] at hNotNodup
  | succ n ih =>
      by_cases hHead : x ∈ orbitList f (f x) n
      · rcases (mem_orbitList_iff f (f x) x n).mp hHead with
          ⟨k, hk, hValue⟩
        refine ⟨0, k + 1, by omega, by omega, ?_⟩
        rw [← iterate_succ_start]
        simpa [iterate] using hValue.symm
      · have hTailNotNodup : ¬ (orbitList f (f x) n).Nodup := by
          intro hTailNodup
          apply hNotNodup
          exact List.nodup_cons.mpr ⟨hHead, hTailNodup⟩
        rcases ih (f x) hTailNotNodup with ⟨i, j, hij, hjn, hEqual⟩
        refine ⟨i + 1, j + 1, by omega, by omega, ?_⟩
        rw [← iterate_succ_start, ← iterate_succ_start]
        exact hEqual

theorem finite_orbit_has_repeat {alpha : Type} [BEq alpha]
    [LawfulBEq alpha] (cover : List alpha)
    (hCover : forall x : alpha, x ∈ cover)
    (f : alpha -> alpha) (x : alpha) :
    exists i j : Nat,
      i < j /\ j < cover.length + 1 /\
      iterate f i x = iterate f j x := by
  have hNotNodup :
      ¬ (orbitList f x (cover.length + 1)).Nodup := by
    intro hNodup
    have hLength := nodup_length_le_of_cover
      (orbitList f x (cover.length + 1)) cover hNodup
      (fun y _ => hCover y)
    rw [orbitList_length] at hLength
    omega
  exact orbit_not_nodup_has_repeat f x (cover.length + 1) hNotNodup

structure FixedPointFreeInvolution (alpha : Type) where
  mate : alpha -> alpha
  involutive : forall x, mate (mate x) = x
  no_fixed_point : forall x, mate x ≠ x

def successor {alpha : Type}
    (localMate sharedMate : FixedPointFreeInvolution alpha)
    (x : alpha) : alpha :=
  sharedMate.mate (localMate.mate x)

def predecessor {alpha : Type}
    (localMate sharedMate : FixedPointFreeInvolution alpha)
    (x : alpha) : alpha :=
  localMate.mate (sharedMate.mate x)

theorem predecessor_successor {alpha : Type}
    (localMate sharedMate : FixedPointFreeInvolution alpha) (x : alpha) :
    predecessor localMate sharedMate (successor localMate sharedMate x) = x := by
  unfold predecessor successor
  rw [sharedMate.involutive, localMate.involutive]

theorem successor_predecessor {alpha : Type}
    (localMate sharedMate : FixedPointFreeInvolution alpha) (x : alpha) :
    successor localMate sharedMate (predecessor localMate sharedMate x) = x := by
  unfold predecessor successor
  rw [localMate.involutive, sharedMate.involutive]

theorem inverse_iterates_cancel {alpha : Type} (f g : alpha -> alpha)
    (hLeft : forall x, g (f x) = x) (n : Nat) (x : alpha) :
    iterate g n (iterate f n x) = x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      calc
        iterate g (n + 1) (iterate f (n + 1) x) =
            iterate g n (g (iterate f (n + 1) x)) := by
              rw [iterate_succ_start]
        _ = iterate g n (g (f (iterate f n x))) := by
              rfl
        _ = iterate g n (iterate f n x) := by
              rw [hLeft]
        _ = x := ih x

theorem repeat_of_inverse_has_positive_period {alpha : Type}
    (f g : alpha -> alpha) (hLeft : forall x, g (f x) = x)
    (x : alpha) {i j : Nat} (hij : i < j)
    (hRepeat : iterate f i x = iterate f j x) :
    exists period : Nat, 0 < period /\ iterate f period x = x := by
  let period := j - i
  have hPeriodPos : 0 < period := by
    dsimp [period]
    omega
  have hIndex : i + period = j := by
    dsimp [period]
    omega
  have hExpanded :
      iterate f i x = iterate f i (iterate f period x) := by
    calc
      iterate f i x = iterate f j x := hRepeat
      _ = iterate f (i + period) x := by rw [hIndex]
      _ = iterate f i (iterate f period x) := iterate_add f i period x
  have hCancelled := congrArg (iterate g i) hExpanded
  have hClosed : x = iterate f period x := by
    calc
      x = iterate g i (iterate f i x) :=
        (inverse_iterates_cancel f g hLeft i x).symm
      _ = iterate g i (iterate f i (iterate f period x)) := hCancelled
      _ = iterate f period x :=
        inverse_iterates_cancel f g hLeft i (iterate f period x)
  exact ⟨period, hPeriodPos, hClosed.symm⟩

structure FiniteAlternatingTraversal (alpha : Type) [BEq alpha] where
  localMate : FixedPointFreeInvolution alpha
  sharedMate : FixedPointFreeInvolution alpha
  cover : List alpha
  covers : forall x : alpha, x ∈ cover

theorem every_state_has_closed_cycle {alpha : Type} [BEq alpha]
    [LawfulBEq alpha] (traversal : FiniteAlternatingTraversal alpha)
    (x : alpha) :
    exists period : Nat, 0 < period /\
      iterate (successor traversal.localMate traversal.sharedMate) period x = x := by
  rcases finite_orbit_has_repeat traversal.cover traversal.covers
      (successor traversal.localMate traversal.sharedMate) x with
    ⟨i, j, hij, _, hRepeat⟩
  exact repeat_of_inverse_has_positive_period
    (successor traversal.localMate traversal.sharedMate)
    (predecessor traversal.localMate traversal.sharedMate)
    (predecessor_successor traversal.localMate traversal.sharedMate)
    x hij hRepeat

end FiniteAlternatingCycleKernel
end BoundaryOfSelf
