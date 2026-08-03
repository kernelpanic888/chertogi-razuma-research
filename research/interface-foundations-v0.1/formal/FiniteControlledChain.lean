import ControlledEquivComposition

namespace BoundaryOfSelf
namespace FiniteControlledChain

noncomputable section

open Filter
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport
open ControlledEquivComposition
open scoped BigOperators

universe u

variable {X : Type u} [PseudoMetricSpace X]

/-!
IF-BS-22F-F5 folds arbitrary finite lists of controlled self-equivalences. It
then studies finite prefixes of an infinite sequence. A uniform bound on the
prefix products is sufficient for the moving-interface approximation error to
tend to zero. No common limiting interface is asserted.
-/

def composeControlledList : List (ControlledEquiv X X) → ControlledEquiv X X
  | [] => identityControlledEquiv
  | first :: rest => composeControlled first (composeControlledList rest)

@[simp]
theorem composeControlledList_nil :
    composeControlledList ([] : List (ControlledEquiv X X)) =
      identityControlledEquiv := rfl

@[simp]
theorem composeControlledList_cons_apply
    (first : ControlledEquiv X X) (rest : List (ControlledEquiv X X))
    (point : X) :
    composeControlledList (first :: rest) point =
      composeControlledList rest (first point) := rfl

theorem composeControlledList_forwardConstant
    (chain : List (ControlledEquiv X X)) :
    (composeControlledList chain).forwardConstant =
      (chain.map (fun controlled => controlled.forwardConstant)).prod := by
  induction chain with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp [composeControlledList, inductionHypothesis, mul_comm]

theorem composeControlledList_inverseConstant
    (chain : List (ControlledEquiv X X)) :
    (composeControlledList chain).inverseConstant =
      (chain.map (fun controlled => controlled.inverseConstant)).prod := by
  induction chain with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp [composeControlledList, inductionHypothesis]

theorem composeControlledList_append_apply
    (firstPart secondPart : List (ControlledEquiv X X)) (point : X) :
    composeControlledList (firstPart ++ secondPart) point =
      composeControlledList secondPart (composeControlledList firstPart point) := by
  induction firstPart generalizing point with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simpa [composeControlledList] using inductionHypothesis (first point)

def chainComputableBoundaryModel
    (chain : List (ControlledEquiv X X)) (model : ComputableBoundaryModel X) :
    ComputableBoundaryModel X :=
  transportComputableBoundaryModel (composeControlledList chain) model

theorem finite_chain_model_error_le
    (chain : List (ControlledEquiv X X)) (model : ComputableBoundaryModel X)
    (n : Nat) :
    Metric.hausdorffDist
      ((chainComputableBoundaryModel chain model).approximation.carrier n)
      (chainComputableBoundaryModel chain model).interface ≤
    (chain.map (fun controlled => controlled.forwardConstant)).prod *
      model.approximation.envelope n := by
  have transported := transported_model_error_le
    (composeControlledList chain) model n
  rw [composeControlledList_forwardConstant] at transported
  exact transported

theorem finite_chain_model_converges_to_actual_frontier
    (chain : List (ControlledEquiv X X)) (model : ComputableBoundaryModel X) :
    Tendsto
      (fun n => Metric.hausdorffDist
        ((chainComputableBoundaryModel chain model).approximation.carrier n)
        (frontier (chainComputableBoundaryModel chain model).inside))
      atTop (nhds 0) := by
  exact transported_model_converges_to_actual_frontier
    (composeControlledList chain) model

theorem finite_chain_interface_is_actual_frontier
    (chain : List (ControlledEquiv X X)) (model : ComputableBoundaryModel X) :
    frontier (chainComputableBoundaryModel chain model).inside =
      (chainComputableBoundaryModel chain model).interface :=
  (chainComputableBoundaryModel chain model).interface_is_frontier

def prefixControlledEquiv
    (sequence : Nat → ControlledEquiv X X) : Nat → ControlledEquiv X X
  | 0 => identityControlledEquiv
  | n + 1 => composeControlled (prefixControlledEquiv sequence n) (sequence n)

def prefixForwardProduct
    (sequence : Nat → ControlledEquiv X X) (n : Nat) : NNReal :=
  ∏ index ∈ Finset.range n, (sequence index).forwardConstant

@[simp]
theorem prefixForwardProduct_zero
    (sequence : Nat → ControlledEquiv X X) :
    prefixForwardProduct sequence 0 = 1 := by
  simp [prefixForwardProduct]

theorem prefixForwardProduct_succ
    (sequence : Nat → ControlledEquiv X X) (n : Nat) :
    prefixForwardProduct sequence (n + 1) =
      prefixForwardProduct sequence n * (sequence n).forwardConstant := by
  simp [prefixForwardProduct, Finset.prod_range_succ]

theorem prefixControlledEquiv_forwardConstant
    (sequence : Nat → ControlledEquiv X X) (n : Nat) :
    (prefixControlledEquiv sequence n).forwardConstant =
      prefixForwardProduct sequence n := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      simp [prefixControlledEquiv, prefixForwardProduct_succ,
        inductionHypothesis, mul_comm]

def prefixComputableBoundaryModel
    (sequence : Nat → ControlledEquiv X X) (depth : Nat)
    (model : ComputableBoundaryModel X) : ComputableBoundaryModel X :=
  transportComputableBoundaryModel (prefixControlledEquiv sequence depth) model

theorem prefix_model_error_le
    (sequence : Nat → ControlledEquiv X X) (depth approximationIndex : Nat)
    (model : ComputableBoundaryModel X) :
    Metric.hausdorffDist
      ((prefixComputableBoundaryModel sequence depth model).approximation.carrier
        approximationIndex)
      (prefixComputableBoundaryModel sequence depth model).interface ≤
    prefixForwardProduct sequence depth *
      model.approximation.envelope approximationIndex := by
  have transported := transported_model_error_le
    (prefixControlledEquiv sequence depth) model approximationIndex
  rw [prefixControlledEquiv_forwardConstant] at transported
  exact transported

theorem model_envelope_nonnegative
    (model : ComputableBoundaryModel X) (n : Nat) :
    0 ≤ model.approximation.envelope n :=
  le_trans Metric.hausdorffDist_nonneg (model.approximation.hausdorff_le n)

theorem bounded_prefix_scaled_envelope_tendsto_zero
    (sequence : Nat → ControlledEquiv X X) (model : ComputableBoundaryModel X)
    (bound : Real)
    (hBound : forall n, (prefixForwardProduct sequence n : Real) ≤ bound) :
    Tendsto
      (fun n => (prefixForwardProduct sequence n : Real) *
        model.approximation.envelope n)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact mul_nonneg (NNReal.coe_nonneg _) (model_envelope_nonnegative model n)
  · intro n
    exact mul_le_mul_of_nonneg_right (hBound n)
      (model_envelope_nonnegative model n)
  · simpa using tendsto_const_nhds.mul model.approximation.envelope_tendsto_zero

theorem bounded_prefix_moving_error_tendsto_zero
    (sequence : Nat → ControlledEquiv X X) (model : ComputableBoundaryModel X)
    (bound : Real)
    (hBound : forall n, (prefixForwardProduct sequence n : Real) ≤ bound) :
    Tendsto
      (fun n => Metric.hausdorffDist
        ((prefixComputableBoundaryModel sequence n model).approximation.carrier n)
        (prefixComputableBoundaryModel sequence n model).interface)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact Metric.hausdorffDist_nonneg
  · intro n
    exact prefix_model_error_le sequence n n model
  · exact bounded_prefix_scaled_envelope_tendsto_zero sequence model bound hBound

theorem prefix_interface_is_actual_frontier
    (sequence : Nat → ControlledEquiv X X) (depth : Nat)
    (model : ComputableBoundaryModel X) :
    frontier (prefixComputableBoundaryModel sequence depth model).inside =
      (prefixComputableBoundaryModel sequence depth model).interface :=
  (prefixComputableBoundaryModel sequence depth model).interface_is_frontier

end
end FiniteControlledChain
end BoundaryOfSelf
