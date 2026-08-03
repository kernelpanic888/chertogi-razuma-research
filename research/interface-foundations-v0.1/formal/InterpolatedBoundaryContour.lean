import UniformRadialBoundaryFamily

namespace BoundaryOfSelf
namespace InterpolatedBoundaryContour

open RationalBoundaryLimit
open RefinedCurvedBoundaryGrid
open UniformRadialBoundaryFamily

/-!
IF-BS-10 assigns an exact piecewise-linear level crossing to every discrete
crossing edge. The metric used here is normalized arclength along that edge.
No planar Hausdorff theorem is claimed in this module.
-/

theorem unitAdjacent_comm {m : Nat} {p q : GridSample m}
    (h : UnitAdjacent p q) : UnitAdjacent q p := by
  rcases h with ⟨hy, hx⟩ | ⟨hx, hy⟩
  · left
    exact ⟨hy.symm, hx.elim Or.inr Or.inl⟩
  · right
    exact ⟨hx.symm, hy.elim Or.inr Or.inl⟩

structure CrossingEdge (m : Nat) where
  p : GridSample m
  q : GridSample m
  adjacent : UnitAdjacent p q
  crosses : Crosses p q

def innerPoint {m : Nat} (e : CrossingEdge m) : GridSample m :=
  if radialNumerator e.p <= thresholdNumerator m then e.p else e.q

def outerPoint {m : Nat} (e : CrossingEdge m) : GridSample m :=
  if radialNumerator e.p <= thresholdNumerator m then e.q else e.p

theorem innerPoint_inside {m : Nat} (e : CrossingEdge m) :
    Inside (innerPoint e) := by
  rcases e.crosses with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · unfold Inside at hp hq ⊢
    simp [innerPoint, hp]
  · unfold Inside at hp hq ⊢
    simp [innerPoint, hp, hq]

theorem outerPoint_outside {m : Nat} (e : CrossingEdge m) :
    ¬ Inside (outerPoint e) := by
  rcases e.crosses with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · unfold Inside at hp hq ⊢
    simp [outerPoint, hp, hq]
  · unfold Inside at hp hq ⊢
    simp [outerPoint, hp]

theorem oriented_points_adjacent {m : Nat} (e : CrossingEdge m) :
    UnitAdjacent (innerPoint e) (outerPoint e) := by
  rcases e.crosses with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · unfold Inside at hp hq
    simpa [innerPoint, outerPoint, hp] using e.adjacent
  · unfold Inside at hp hq
    simpa [innerPoint, outerPoint, hp] using unitAdjacent_comm e.adjacent

def interpolationDenominator {m : Nat} (e : CrossingEdge m) : Nat :=
  radialNumerator (outerPoint e) - radialNumerator (innerPoint e)

def interpolationNumerator {m : Nat} (e : CrossingEdge m) : Nat :=
  thresholdNumerator m - radialNumerator (innerPoint e)

theorem interpolationDenominator_pos {m : Nat} (e : CrossingEdge m) :
    0 < interpolationDenominator e := by
  have hi := innerPoint_inside e
  have ho := outerPoint_outside e
  unfold Inside at hi ho
  unfold interpolationDenominator
  omega

theorem interpolationNumerator_le_denominator {m : Nat}
    (e : CrossingEdge m) :
    interpolationNumerator e <= interpolationDenominator e := by
  have hi := innerPoint_inside e
  have ho := outerPoint_outside e
  unfold Inside at hi ho
  unfold interpolationNumerator interpolationDenominator
  omega

structure UnitIntervalFraction where
  numerator : Nat
  denominator : Nat
  denominator_pos : 0 < denominator
  numerator_le_denominator : numerator <= denominator

def interpolationParameter {m : Nat}
    (e : CrossingEdge m) : UnitIntervalFraction where
  numerator := interpolationNumerator e
  denominator := interpolationDenominator e
  denominator_pos := interpolationDenominator_pos e
  numerator_le_denominator := interpolationNumerator_le_denominator e

theorem interpolation_hits_threshold {m : Nat} (e : CrossingEdge m) :
    interpolationDenominator e * radialNumerator (innerPoint e) +
      interpolationNumerator e * interpolationDenominator e =
    interpolationDenominator e * thresholdNumerator m := by
  have hi := innerPoint_inside e
  unfold Inside at hi
  have hThreshold :
      thresholdNumerator m = radialNumerator (innerPoint e) +
        interpolationNumerator e := by
    unfold interpolationNumerator
    omega
  calc
    interpolationDenominator e * radialNumerator (innerPoint e) +
        interpolationNumerator e * interpolationDenominator e =
      interpolationDenominator e * radialNumerator (innerPoint e) +
        interpolationDenominator e * interpolationNumerator e := by
          rw [Nat.mul_comm (interpolationNumerator e)]
    _ = interpolationDenominator e *
        (radialNumerator (innerPoint e) + interpolationNumerator e) := by
          rw [Nat.mul_add]
    _ = interpolationDenominator e * thresholdNumerator m := by
          rw [← hThreshold]

structure NonnegativeFraction where
  numerator : Nat
  denominator : Nat
  denominator_pos : 0 < denominator

def FractionLePositive (a : NonnegativeFraction)
    (b : PositiveFraction) : Prop :=
  a.numerator * b.denominator <= b.numerator * a.denominator

def innerArcDistance {m : Nat} (hm : 0 < m)
    (e : CrossingEdge m) : NonnegativeFraction where
  numerator := interpolationNumerator e
  denominator := interpolationDenominator e * m
  denominator_pos := Nat.mul_pos (interpolationDenominator_pos e) hm

def outerArcDistance {m : Nat} (hm : 0 < m)
    (e : CrossingEdge m) : NonnegativeFraction where
  numerator := interpolationDenominator e - interpolationNumerator e
  denominator := interpolationDenominator e * m
  denominator_pos := Nat.mul_pos (interpolationDenominator_pos e) hm

theorem innerArcDistance_le_cellWidth {m : Nat} (hm : 0 < m)
    (e : CrossingEdge m) :
    FractionLePositive (innerArcDistance hm e) (cellWidth m hm) := by
  change interpolationNumerator e * m <=
    1 * (interpolationDenominator e * m)
  simp only [Nat.one_mul]
  exact Nat.mul_le_mul_right m (interpolationNumerator_le_denominator e)

theorem outerArcDistance_le_cellWidth {m : Nat} (hm : 0 < m)
    (e : CrossingEdge m) :
    FractionLePositive (outerArcDistance hm e) (cellWidth m hm) := by
  change (interpolationDenominator e - interpolationNumerator e) * m <=
    1 * (interpolationDenominator e * m)
  simp only [Nat.one_mul]
  have hSub : interpolationDenominator e - interpolationNumerator e <=
      interpolationDenominator e := by omega
  exact Nat.mul_le_mul_right m hSub

theorem interpolated_contour_mesh_limit :
    forall epsilon : PositiveFraction, exists N : Nat,
      0 < N /\ forall (m : Nat) (hm : 0 < m), N <= m ->
        FractionLt (cellWidth m hm) epsilon /\
        forall e : CrossingEdge m,
          FractionLePositive (innerArcDistance hm e) (cellWidth m hm) /\
          FractionLePositive (outerArcDistance hm e) (cellWidth m hm) := by
  intro epsilon
  rcases rational_epsilon_limit epsilon with ⟨N, hN, hLimit⟩
  refine ⟨N, hN, ?_⟩
  intro m hm hNm
  refine ⟨hLimit m hm hNm, ?_⟩
  intro e
  exact ⟨innerArcDistance_le_cellWidth hm e,
    outerArcDistance_le_cellWidth hm e⟩

end InterpolatedBoundaryContour
end BoundaryOfSelf
