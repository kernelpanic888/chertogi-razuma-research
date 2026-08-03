import DiagonalEllipseFamily

namespace BoundaryOfSelf
namespace ControlledEquivComposition

noncomputable section

open Filter
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport

universe u v w q

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type q}
variable [PseudoMetricSpace X] [PseudoMetricSpace Y]
variable [PseudoMetricSpace Z] [PseudoMetricSpace W]

/-!
IF-BS-22F-F4 gives controlled boundary transport a compositional law. If
F : X -> Y has constants L_F, M_F and G : Y -> Z has constants L_G, M_G,
then G after F has forward constant L_G L_F and inverse constant M_F M_G.
-/

def composeControlled (first : ControlledEquiv X Y)
    (second : ControlledEquiv Y Z) : ControlledEquiv X Z where
  toHomeomorph := first.toHomeomorph.trans second.toHomeomorph
  forwardConstant := second.forwardConstant * first.forwardConstant
  inverseConstant := first.inverseConstant * second.inverseConstant
  forward_lipschitz := by
    change LipschitzWith (second.forwardConstant * first.forwardConstant)
      (fun point => second (first point))
    exact second.forward_lipschitz.comp first.forward_lipschitz
  inverse_lipschitz := by
    change LipschitzWith (first.inverseConstant * second.inverseConstant)
      (fun point => first.toHomeomorph.symm (second.toHomeomorph.symm point))
    exact first.inverse_lipschitz.comp second.inverse_lipschitz

@[simp]
theorem composeControlled_apply (first : ControlledEquiv X Y)
    (second : ControlledEquiv Y Z) (point : X) :
    composeControlled first second point = second (first point) := rfl

@[simp]
theorem composeControlled_symm_apply (first : ControlledEquiv X Y)
    (second : ControlledEquiv Y Z) (point : Z) :
    (composeControlled first second).toHomeomorph.symm point =
      first.toHomeomorph.symm (second.toHomeomorph.symm point) := rfl

@[simp]
theorem composeControlled_forwardConstant (first : ControlledEquiv X Y)
    (second : ControlledEquiv Y Z) :
    (composeControlled first second).forwardConstant =
      second.forwardConstant * first.forwardConstant := rfl

@[simp]
theorem composeControlled_inverseConstant (first : ControlledEquiv X Y)
    (second : ControlledEquiv Y Z) :
    (composeControlled first second).inverseConstant =
      first.inverseConstant * second.inverseConstant := rfl

def identityControlledEquiv : ControlledEquiv X X where
  toHomeomorph := Homeomorph.refl X
  forwardConstant := 1
  inverseConstant := 1
  forward_lipschitz := LipschitzWith.id
  inverse_lipschitz := LipschitzWith.id

@[simp]
theorem identityControlledEquiv_apply (point : X) :
    (identityControlledEquiv : ControlledEquiv X X) point = point := rfl

theorem composeControlled_left_identity_apply
    (controlled : ControlledEquiv X Y) (point : X) :
    composeControlled identityControlledEquiv controlled point = controlled point := rfl

theorem composeControlled_right_identity_apply
    (controlled : ControlledEquiv X Y) (point : X) :
    composeControlled controlled identityControlledEquiv point = controlled point := rfl

theorem composeControlled_associative_apply
    (first : ControlledEquiv X Y) (second : ControlledEquiv Y Z)
    (third : ControlledEquiv Z W) (point : X) :
    composeControlled (composeControlled first second) third point =
      composeControlled first (composeControlled second third) point := rfl

theorem composeControlled_associative_forwardConstant
    (first : ControlledEquiv X Y) (second : ControlledEquiv Y Z)
    (third : ControlledEquiv Z W) :
    (composeControlled (composeControlled first second) third).forwardConstant =
      (composeControlled first (composeControlled second third)).forwardConstant := by
  simp [mul_assoc]

theorem composeControlled_associative_inverseConstant
    (first : ControlledEquiv X Y) (second : ControlledEquiv Y Z)
    (third : ControlledEquiv Z W) :
    (composeControlled (composeControlled first second) third).inverseConstant =
      (composeControlled first (composeControlled second third)).inverseConstant := by
  simp [mul_assoc]

def composedComputableBoundaryModel (first : ControlledEquiv X Y)
    (second : ControlledEquiv Y Z) (model : ComputableBoundaryModel X) :
    ComputableBoundaryModel Z :=
  transportComputableBoundaryModel (composeControlled first second) model

theorem composed_model_error_le (first : ControlledEquiv X Y)
    (second : ControlledEquiv Y Z) (model : ComputableBoundaryModel X)
    (n : Nat) :
    Metric.hausdorffDist
      ((composedComputableBoundaryModel first second model).approximation.carrier n)
      (composedComputableBoundaryModel first second model).interface ≤
    (second.forwardConstant * first.forwardConstant) *
      model.approximation.envelope n := by
  exact transported_model_error_le (composeControlled first second) model n

theorem composed_model_converges_to_actual_frontier
    (first : ControlledEquiv X Y) (second : ControlledEquiv Y Z)
    (model : ComputableBoundaryModel X) :
    Tendsto
      (fun n => Metric.hausdorffDist
        ((composedComputableBoundaryModel first second model).approximation.carrier n)
        (frontier (composedComputableBoundaryModel first second model).inside))
      atTop (nhds 0) := by
  exact transported_model_converges_to_actual_frontier
    (composeControlled first second) model

theorem composed_model_interface_is_actual_frontier
    (first : ControlledEquiv X Y) (second : ControlledEquiv Y Z)
    (model : ComputableBoundaryModel X) :
    frontier (composedComputableBoundaryModel first second model).inside =
      (composedComputableBoundaryModel first second model).interface :=
  (composedComputableBoundaryModel first second model).interface_is_frontier

end
end ControlledEquivComposition
end BoundaryOfSelf
