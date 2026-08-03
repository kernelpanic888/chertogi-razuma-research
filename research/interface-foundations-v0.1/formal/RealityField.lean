namespace RealityField

universe u v

abbrev Distinguishability (S : Type u) := S -> S -> Nat

def AbsoluteMerge {S : Type u}
    (D : Distinguishability S) (a b : S) : Prop :=
  D a b = 0

def LocalPole {S : Type u}
    (D : Distinguishability S) (epsilon : Nat) (a b : S) : Prop :=
  0 < D a b ∧ D a b <= epsilon

def Resolved {S : Type u}
    (D : Distinguishability S) (epsilon : Nat) (a b : S) : Prop :=
  epsilon < D a b

def ReturnAt {X : Type u}
    (Equivalent : X -> X -> Prop) (gamma : Nat -> X) (turn : Nat) : Prop :=
  Equivalent (gamma turn) (gamma 0)

def TwoTurnReturn {X : Type u}
    (Equivalent : X -> X -> Prop) (gamma : Nat -> X) : Prop :=
  ¬ ReturnAt Equivalent gamma 1 ∧ ReturnAt Equivalent gamma 2

def PreservesInvariant {X : Type u} {I : Type v}
    (Admissible : X -> X -> Prop) (Inv : X -> I) : Prop :=
  ∀ {x y : X}, Admissible x y -> Inv x = Inv y

def MonopoleWitness (flux : Int) : Prop :=
  flux ≠ 0

def ThisPhysics (globalPotential : Prop) (flux : Int) : Prop :=
  globalPotential ∧ flux = 0

theorem localPole_excludes_absoluteMerge
    {S : Type u} (D : Distinguishability S) (epsilon : Nat) (a b : S)
    (hPole : LocalPole D epsilon a b) :
    ¬ AbsoluteMerge D a b := by
  intro hMerge
  unfold AbsoluteMerge at hMerge
  unfold LocalPole at hPole
  rw [hMerge] at hPole
  exact Nat.lt_irrefl 0 hPole.1

theorem resolved_excludes_localPole
    {S : Type u} (D : Distinguishability S) (epsilon : Nat) (a b : S)
    (hResolved : Resolved D epsilon a b) :
    ¬ LocalPole D epsilon a b := by
  intro hPole
  exact Nat.not_lt_of_ge hPole.2 hResolved

theorem twoTurnReturn_keeps_oneTurn_nontrivial
    {X : Type u} (Equivalent : X -> X -> Prop) (gamma : Nat -> X)
    (hReturn : TwoTurnReturn Equivalent gamma) :
    ¬ ReturnAt Equivalent gamma 1 :=
  hReturn.1

theorem invariant_change_forces_nonadmissibility
    {X : Type u} {I : Type v}
    (Admissible : X -> X -> Prop) (Inv : X -> I) (x y : X)
    (hPreserved : PreservesInvariant Admissible Inv)
    (hChanged : Inv x ≠ Inv y) :
    ¬ Admissible x y := by
  intro hAdmissible
  exact hChanged (hPreserved hAdmissible)

theorem monopole_is_external_to_thisPhysics
    (globalPotential : Prop) (flux : Int)
    (hPhysics : ThisPhysics globalPotential flux) :
    ¬ MonopoleWitness flux := by
  intro hMonopole
  exact hMonopole hPhysics.2

theorem monopole_refutes_thisPhysics
    (globalPotential : Prop) (flux : Int)
    (hMonopole : MonopoleWitness flux) :
    ¬ ThisPhysics globalPotential flux := by
  intro hPhysics
  exact hMonopole hPhysics.2

end RealityField

#print axioms RealityField.localPole_excludes_absoluteMerge
#print axioms RealityField.resolved_excludes_localPole
#print axioms RealityField.twoTurnReturn_keeps_oneTurn_nontrivial
#print axioms RealityField.invariant_change_forces_nonadmissibility
#print axioms RealityField.monopole_is_external_to_thisPhysics
#print axioms RealityField.monopole_refutes_thisPhysics

