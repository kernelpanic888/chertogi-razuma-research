import DominantAxisReverseCoverage

namespace BoundaryOfSelf
namespace HausdorffStyleConvergence

noncomputable section

open InterpolatedBoundaryContour
open LocalPolygonalContour
open LocalSegmentRealCompletion
open OneSidedEuclideanContourBound
open ReverseCoverageMetricAdapter
open ConcreteRadialContourTraversal
open DominantAxisReverseCoverage

/-!
IF-BS-22F-B3D packages the two directed estimates as one explicit
Hausdorff-style pointwise criterion. No Metric instance is imposed on the
authorial point structure: the criterion records the two witness directions
directly through the already audited Euclidean distance.
-/

def hausdorffEnvelope (m : Nat) : Real :=
  4 / (m : Real)

abbrev HausdorffStyleApproximation (m : Nat) (bound : Real) : Prop :=
  BidirectionalCircleApproximation m bound bound

theorem euclideanEnvelope_le_hausdorffEnvelope {m : Nat} (hm : 0 < m) :
    euclideanEnvelope m <= hausdorffEnvelope m := by
  have hmReal : (0 : Real) < m := by
    exact_mod_cast hm
  have hSqrt : Real.sqrt 3 <= 4 := by
    have hSq := Real.sq_sqrt (by norm_num : (0 : Real) <= 3)
    have hNonneg := Real.sqrt_nonneg 3
    nlinarith
  have hInverse : 0 <= (1 / (m : Real)) := by
    positivity
  unfold euclideanEnvelope hausdorffEnvelope
  calc
    Real.sqrt 3 / (m : Real) = Real.sqrt 3 * (1 / (m : Real)) := by ring
    _ <= 4 * (1 / (m : Real)) := mul_le_mul_of_nonneg_right hSqrt hInverse
    _ = 4 / (m : Real) := by ring

theorem hausdorffStyleApproximation_mono {m : Nat} {bound epsilon : Real}
    (approximation : HausdorffStyleApproximation m bound)
    (hBound : bound <= epsilon) :
    HausdorffStyleApproximation m epsilon := by
  constructor
  · intro segment firstVertex secondVertex t ht0 ht1
    rcases approximation.contour_to_circle segment firstVertex secondVertex t ht0 ht1 with
      ⟨target, hTarget, hDistance⟩
    exact ⟨target, hTarget, le_trans hDistance hBound⟩
  · refine { covers := ?_ }
    intro target hTarget
    rcases approximation.circle_to_contour.covers target hTarget with
      ⟨segment, firstVertex, secondVertex, t, ht0, ht1, hDistance⟩
    exact ⟨segment, firstVertex, secondVertex, t, ht0, ht1,
      le_trans hDistance hBound⟩

theorem dominant_axis_hausdorff_style {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) :
    HausdorffStyleApproximation m (hausdorffEnvelope m) := by
  have approximation := dominant_axis_bidirectional_approximation hm anchor
  constructor
  · intro segment firstVertex secondVertex t ht0 ht1
    rcases approximation.contour_to_circle segment firstVertex secondVertex t ht0 ht1 with
      ⟨target, hTarget, hDistance⟩
    exact ⟨target, hTarget,
      le_trans hDistance (euclideanEnvelope_le_hausdorffEnvelope hm)⟩
  · simpa [hausdorffEnvelope] using approximation.circle_to_contour

theorem hausdorffEnvelope_eventually_lt
    (epsilon : Real) (hEpsilon : 0 < epsilon) :
    exists N : Nat, 0 < N /\ forall m : Nat, N <= m ->
      hausdorffEnvelope m < epsilon := by
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / epsilon)
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  intro m hm
  have hNmNat : N < m := lt_of_lt_of_le (Nat.lt_succ_self N) hm
  have hNmReal : (N : Real) < (m : Real) := by
    exact_mod_cast hNmNat
  have hRatio : 4 / epsilon < (m : Real) := lt_trans hN hNmReal
  have hmPos : (0 : Real) < m := by
    exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_succ N) hm)
  have hProduct : (4 : Real) < (m : Real) * epsilon :=
    (div_lt_iff₀ hEpsilon).1 hRatio
  unfold hausdorffEnvelope
  apply (div_lt_iff₀ hmPos).2
  simpa [mul_comm] using hProduct

theorem finite_contours_converge_hausdorff_style
    (epsilon : Real) (hEpsilon : 0 < epsilon) :
    exists N : Nat, 0 < N /\ forall m : Nat, N <= m ->
      forall _anchor : ContourState m,
        HausdorffStyleApproximation m epsilon := by
  obtain ⟨N, hNPos, hN⟩ := hausdorffEnvelope_eventually_lt epsilon hEpsilon
  refine ⟨N, hNPos, ?_⟩
  intro m hm anchor
  have hmPos : 0 < m := lt_of_lt_of_le hNPos hm
  exact hausdorffStyleApproximation_mono
    (dominant_axis_hausdorff_style hmPos anchor) (le_of_lt (hN m hm))

end
end HausdorffStyleConvergence
end BoundaryOfSelf

#print axioms BoundaryOfSelf.HausdorffStyleConvergence.euclideanEnvelope_le_hausdorffEnvelope
#print axioms BoundaryOfSelf.HausdorffStyleConvergence.dominant_axis_hausdorff_style
#print axioms BoundaryOfSelf.HausdorffStyleConvergence.hausdorffEnvelope_eventually_lt
#print axioms BoundaryOfSelf.HausdorffStyleConvergence.finite_contours_converge_hausdorff_style
