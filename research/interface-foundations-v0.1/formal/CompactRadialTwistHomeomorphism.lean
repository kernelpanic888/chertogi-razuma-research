import CompactPlanarSlabWitness
import AnisotropicEllipseChamber

namespace BoundaryOfSelf
namespace CompactRadialTwistHomeomorphism

noncomputable section

open Set
open StandardHausdorffMetricBridge
open OneSidedEuclideanContourBound
open ConcreteRadialContourTraversal
open BoundarySeparationInvariant
open AnisotropicEllipseChamber
open CompactTentHomeomorphism

def rotatePoint (angle : Real) (point : AmbientPlane) : AmbientPlane :=
  planeEmbedding
    { x := Real.cos angle * point 0 - Real.sin angle * point 1
      y := Real.sin angle * point 0 + Real.cos angle * point 1 }

@[simp]
theorem rotatePoint_apply_zero (angle : Real) (point : AmbientPlane) :
    rotatePoint angle point 0 =
      Real.cos angle * point 0 - Real.sin angle * point 1 := by
  simp [rotatePoint, planeEmbedding]

@[simp]
theorem rotatePoint_apply_one (angle : Real) (point : AmbientPlane) :
    rotatePoint angle point 1 =
      Real.sin angle * point 0 + Real.cos angle * point 1 := by
  simp [rotatePoint, planeEmbedding]

theorem rotatePoint_norm_sq (angle : Real) (point : AmbientPlane) :
    ‖rotatePoint angle point‖ ^ 2 = ‖point‖ ^ 2 := by
  rw [ambient_norm_sq_eq_coordinates, ambient_norm_sq_eq_coordinates]
  simp only [rotatePoint_apply_zero, rotatePoint_apply_one]
  have hTrig := Real.sin_sq_add_cos_sq angle
  nlinarith

@[simp]
theorem rotatePoint_norm (angle : Real) (point : AmbientPlane) :
    ‖rotatePoint angle point‖ = ‖point‖ := by
  have hSquared := rotatePoint_norm_sq angle point
  nlinarith [norm_nonneg (rotatePoint angle point), norm_nonneg point]

theorem rotatePoint_add (firstAngle secondAngle : Real)
    (point : AmbientPlane) :
    rotatePoint firstAngle (rotatePoint secondAngle point) =
      rotatePoint (firstAngle + secondAngle) point := by
  ext i
  fin_cases i <;>
    simp [rotatePoint, planeEmbedding, Real.cos_add, Real.sin_add] <;> ring

@[simp]
theorem rotatePoint_zero (point : AmbientPlane) :
    rotatePoint 0 point = point := by
  ext i
  fin_cases i <;> simp [rotatePoint, planeEmbedding]

@[simp]
theorem rotatePoint_neg_comp (angle : Real) (point : AmbientPlane) :
    rotatePoint (-angle) (rotatePoint angle point) = point := by
  rw [rotatePoint_add]
  simp

@[simp]
theorem rotatePoint_comp_neg (angle : Real) (point : AmbientPlane) :
    rotatePoint angle (rotatePoint (-angle) point) = point := by
  rw [rotatePoint_add]
  simp

def radialTwistAngle (amplitude : Real) (point : AmbientPlane) : Real :=
  amplitude * tentBump ‖point‖

def radialTwistMap (amplitude : Real) (point : AmbientPlane) : AmbientPlane :=
  rotatePoint (radialTwistAngle amplitude point) point

@[simp]
theorem radialTwistMap_norm (amplitude : Real) (point : AmbientPlane) :
    ‖radialTwistMap amplitude point‖ = ‖point‖ := by
  exact rotatePoint_norm _ _

@[simp]
theorem radialTwistMap_neg_comp (amplitude : Real) (point : AmbientPlane) :
    radialTwistMap (-amplitude) (radialTwistMap amplitude point) = point := by
  rw [radialTwistMap, radialTwistAngle, radialTwistMap_norm]
  rw [radialTwistMap, radialTwistAngle]
  rw [rotatePoint_add]
  rw [show -amplitude * tentBump ‖point‖ +
    amplitude * tentBump ‖point‖ = 0 by ring]
  exact rotatePoint_zero point

@[simp]
theorem radialTwistMap_comp_neg (amplitude : Real) (point : AmbientPlane) :
    radialTwistMap amplitude (radialTwistMap (-amplitude) point) = point := by
  simpa using radialTwistMap_neg_comp (-amplitude) point

theorem radialTwistAngle_continuous (amplitude : Real) :
    Continuous (radialTwistAngle amplitude) := by
  exact continuous_const.mul
    (tentBump_lipschitz.continuous.comp continuous_norm)

theorem radialTwistMap_continuous (amplitude : Real) :
    Continuous (radialTwistMap amplitude) := by
  have hAngle : Continuous (radialTwistAngle amplitude) :=
    radialTwistAngle_continuous amplitude
  unfold radialTwistMap rotatePoint planeEmbedding
  fun_prop

def radialTwistHomeomorph (amplitude : Real) : AmbientPlane ≃ₜ AmbientPlane where
  toEquiv :=
    { toFun := radialTwistMap amplitude
      invFun := radialTwistMap (-amplitude)
      left_inv := radialTwistMap_neg_comp amplitude
      right_inv := radialTwistMap_comp_neg amplitude }
  continuous_toFun := radialTwistMap_continuous amplitude
  continuous_invFun := radialTwistMap_continuous (-amplitude)

@[simp]
theorem radialTwistHomeomorph_apply (amplitude : Real) (point : AmbientPlane) :
    radialTwistHomeomorph amplitude point = radialTwistMap amplitude point := rfl

@[simp]
theorem radialTwistHomeomorph_symm_apply
    (amplitude : Real) (point : AmbientPlane) :
    (radialTwistHomeomorph amplitude).symm point =
      radialTwistMap (-amplitude) point := rfl

def radialTwistSupport : Set AmbientPlane :=
  Metric.closedBall 0 1

theorem radialTwistSupport_compact : IsCompact radialTwistSupport := by
  exact ProperSpace.isCompact_closedBall 0 1

theorem radialTwist_identity_outside
    (amplitude : Real) {point : AmbientPlane}
    (hPoint : point ∉ radialTwistSupport) :
    radialTwistHomeomorph amplitude point = point := by
  have hNorm : 1 <= ‖point‖ := by
    have hDistance : 1 < dist point 0 := by
      simpa [radialTwistSupport, Metric.mem_closedBall] using hPoint
    simpa [dist_zero_right] using le_of_lt hDistance
  rw [radialTwistHomeomorph_apply, radialTwistMap, radialTwistAngle]
  rw [tentBump_eq_zero_of_abs_ge_one (by simpa [abs_of_nonneg (norm_nonneg point)])]
  simp

theorem radialTwist_inverse_identity_outside
    (amplitude : Real) {point : AmbientPlane}
    (hPoint : point ∉ radialTwistSupport) :
    (radialTwistHomeomorph amplitude).symm point = point := by
  change radialTwistHomeomorph (-amplitude) point = point
  exact radialTwist_identity_outside (-amplitude) hPoint

end
end CompactRadialTwistHomeomorphism
end BoundaryOfSelf
