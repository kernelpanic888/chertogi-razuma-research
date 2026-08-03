import GeneralBoundaryMesh

namespace BoundaryOfSelf
namespace RationalBoundaryLimit

open GeneralBoundaryMesh

structure PositiveFraction where
  numerator : Nat
  denominator : Nat
  numerator_pos : 0 < numerator
  denominator_pos : 0 < denominator

def PositiveFraction.value (q : PositiveFraction) : Rat :=
  Rat.normalize (Int.ofNat q.numerator) q.denominator
    (Nat.ne_of_gt q.denominator_pos)

def FractionLt (a b : PositiveFraction) : Prop :=
  a.numerator * b.denominator < b.numerator * a.denominator

structure UnitIntervalPoint where
  numerator : Nat
  denominator : Nat
  denominator_pos : 0 < denominator
  within : numerator <= denominator

def UnitIntervalPoint.value (x : UnitIntervalPoint) : Rat :=
  Rat.normalize (Int.ofNat x.numerator) x.denominator
    (Nat.ne_of_gt x.denominator_pos)

def embedMeshNode {n : Nat} (hn : 0 < n)
    (x : MeshNode n) : UnitIntervalPoint where
  numerator := x.val
  denominator := n
  denominator_pos := hn
  within := by
    have hx := x.isLt
    omega

theorem embedded_left_coordinate
    {n threshold : Nat} (hn : 0 < n)
    (hThreshold : threshold < n) :
    (embedMeshNode hn (leftBoundaryNode hThreshold)).numerator = threshold := by
  rfl

theorem embedded_right_coordinate
    {n threshold : Nat} (hn : 0 < n)
    (hThreshold : threshold < n) :
    (embedMeshNode hn (rightBoundaryNode hThreshold)).numerator =
      threshold + 1 := by
  rfl

theorem embedded_boundary_gap_numerator_is_one
    {n threshold : Nat} (hn : 0 < n)
    (hThreshold : threshold < n) :
    (embedMeshNode hn (rightBoundaryNode hThreshold)).numerator -
      (embedMeshNode hn (leftBoundaryNode hThreshold)).numerator = 1 := by
  simp [embedMeshNode, leftBoundaryNode, rightBoundaryNode]

def cellWidth (n : Nat) (hn : 0 < n) : PositiveFraction where
  numerator := 1
  denominator := n
  numerator_pos := by omega
  denominator_pos := hn

theorem cellWidth_lt_iff
    {n : Nat} (hn : 0 < n) (epsilon : PositiveFraction) :
    FractionLt (cellWidth n hn) epsilon <->
      epsilon.denominator < epsilon.numerator * n := by
  simp [FractionLt, cellWidth]

theorem rational_epsilon_limit :
    forall epsilon : PositiveFraction, exists N : Nat,
      0 < N /\ forall (n : Nat) (hn : 0 < n), N <= n ->
        FractionLt (cellWidth n hn) epsilon := by
  intro epsilon
  refine ⟨epsilon.denominator + 1, by omega, ?_⟩
  intro n hn hN
  apply (cellWidth_lt_iff hn epsilon).mpr
  have hDenominator : epsilon.denominator < n := by
    omega
  have hNumerator : 1 <= epsilon.numerator :=
    epsilon.numerator_pos
  have hScale : n <= epsilon.numerator * n := by
    calc
      n = 1 * n := by simp
      _ <= epsilon.numerator * n := Nat.mul_le_mul_right n hNumerator
  exact Nat.lt_of_lt_of_le hDenominator hScale

theorem boundary_band_below_epsilon
    {n threshold : Nat} (hn : 0 < n)
    (hThreshold : threshold < n)
    (epsilon : PositiveFraction)
    (hSmall : FractionLt (cellWidth n hn) epsilon) :
    BandNode n threshold (leftBoundaryNode hThreshold) /\
      BandNode n threshold (rightBoundaryNode hThreshold) /\
      FractionLt (cellWidth n hn) epsilon := by
  exact ⟨leftBoundaryNode_isBand hThreshold,
    rightBoundaryNode_isBand hThreshold,
    hSmall⟩

end RationalBoundaryLimit
end BoundaryOfSelf

#print axioms BoundaryOfSelf.RationalBoundaryLimit.embedded_boundary_gap_numerator_is_one
#print axioms BoundaryOfSelf.RationalBoundaryLimit.cellWidth_lt_iff
#print axioms BoundaryOfSelf.RationalBoundaryLimit.rational_epsilon_limit
#print axioms BoundaryOfSelf.RationalBoundaryLimit.boundary_band_below_epsilon
