import BiLipschitzBoundaryTransport

namespace BoundaryOfSelf
namespace AnisotropicEllipseChamber

noncomputable section

open Filter
open StandardHausdorffMetricBridge
open OneSidedEuclideanContourBound
open ConcreteRadialContourTraversal
open BoundarySeparationInvariant
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport

/-!
IF-BS-22F-F2 is the first explicit non-circular chamber transported through
the controlled-boundary theorem. The map stretches only the first coordinate:

  F(x,y) = (2x,y),    F^{-1}(x,y) = (x/2,y).

The forward map is 2-Lipschitz, the inverse is 1-Lipschitz, and the transported
circle has the exact equation x^2/4 + y^2 = 2.
-/

def anisotropicLinearEquiv : AmbientPlane ≃ₗ[Real] AmbientPlane where
  toFun point := planeEmbedding { x := 2 * point 0, y := point 1 }
  invFun point := planeEmbedding { x := point 0 / 2, y := point 1 }
  left_inv point := by
    ext i
    fin_cases i <;> simp [planeEmbedding]
  right_inv point := by
    ext i
    fin_cases i <;> simp [planeEmbedding] <;> ring
  map_add' first second := by
    ext i
    fin_cases i <;> simp [planeEmbedding] <;> ring
  map_smul' scalar point := by
    ext i
    fin_cases i <;> simp [planeEmbedding] <;> ring

theorem ambient_norm_sq_eq_coordinates (point : AmbientPlane) :
    ‖point‖ ^ 2 = point 0 ^ 2 + point 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_two]

@[simp]
theorem anisotropic_apply_zero (point : AmbientPlane) :
    anisotropicLinearEquiv point 0 = 2 * point 0 := by
  simp [anisotropicLinearEquiv, planeEmbedding]

@[simp]
theorem anisotropic_apply_one (point : AmbientPlane) :
    anisotropicLinearEquiv point 1 = point 1 := by
  simp [anisotropicLinearEquiv, planeEmbedding]

@[simp]
theorem anisotropic_symm_apply_zero (point : AmbientPlane) :
    anisotropicLinearEquiv.symm point 0 = point 0 / 2 := by
  simp [anisotropicLinearEquiv, planeEmbedding]

@[simp]
theorem anisotropic_symm_apply_one (point : AmbientPlane) :
    anisotropicLinearEquiv.symm point 1 = point 1 := by
  simp [anisotropicLinearEquiv, planeEmbedding]

theorem anisotropic_norm_sq_eq (point : AmbientPlane) :
    ‖anisotropicLinearEquiv point‖ ^ 2 =
      4 * point 0 ^ 2 + point 1 ^ 2 := by
  rw [ambient_norm_sq_eq_coordinates]
  simp
  ring

theorem anisotropic_inverse_norm_sq_eq (point : AmbientPlane) :
    ‖anisotropicLinearEquiv.symm point‖ ^ 2 =
      point 0 ^ 2 / 4 + point 1 ^ 2 := by
  rw [ambient_norm_sq_eq_coordinates]
  simp
  ring

theorem anisotropic_norm_le_two (point : AmbientPlane) :
    ‖anisotropicLinearEquiv point‖ ≤ 2 * ‖point‖ := by
  have hSquared :
      ‖anisotropicLinearEquiv point‖ ^ 2 ≤ (2 * ‖point‖) ^ 2 := by
    calc
      ‖anisotropicLinearEquiv point‖ ^ 2 =
          4 * point 0 ^ 2 + point 1 ^ 2 := anisotropic_norm_sq_eq point
      _ ≤ 4 * (point 0 ^ 2 + point 1 ^ 2) := by
        nlinarith [sq_nonneg (point 1)]
      _ = (2 * ‖point‖) ^ 2 := by
        rw [← ambient_norm_sq_eq_coordinates]
        ring
  have hLeft : 0 ≤ ‖anisotropicLinearEquiv point‖ := norm_nonneg _
  have hRight : 0 ≤ 2 * ‖point‖ := mul_nonneg (by norm_num) (norm_nonneg _)
  nlinarith

theorem anisotropic_inverse_norm_le_one (point : AmbientPlane) :
    ‖anisotropicLinearEquiv.symm point‖ ≤ 1 * ‖point‖ := by
  have hSquared :
      ‖anisotropicLinearEquiv.symm point‖ ^ 2 ≤ ‖point‖ ^ 2 := by
    calc
      ‖anisotropicLinearEquiv.symm point‖ ^ 2 =
          point 0 ^ 2 / 4 + point 1 ^ 2 := anisotropic_inverse_norm_sq_eq point
      _ ≤ point 0 ^ 2 + point 1 ^ 2 := by
        nlinarith [sq_nonneg (point 0)]
      _ = ‖point‖ ^ 2 := by
        rw [ambient_norm_sq_eq_coordinates]
  have hLeft : 0 ≤ ‖anisotropicLinearEquiv.symm point‖ := norm_nonneg _
  have hRight : 0 ≤ ‖point‖ := norm_nonneg _
  nlinarith

def anisotropicContinuousLinearEquiv : AmbientPlane ≃L[Real] AmbientPlane :=
  anisotropicLinearEquiv.toContinuousLinearEquivOfBounds
    2 1 anisotropic_norm_le_two anisotropic_inverse_norm_le_one

theorem anisotropic_forward_lipschitz :
    LipschitzWith 2 anisotropicContinuousLinearEquiv := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  change dist (anisotropicLinearEquiv first) (anisotropicLinearEquiv second) ≤
    (2 : Real) * dist first second
  simpa [dist_eq_norm] using anisotropic_norm_le_two (first - second)

theorem anisotropic_inverse_lipschitz :
    LipschitzWith 1 anisotropicContinuousLinearEquiv.symm := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  change dist (anisotropicLinearEquiv.symm first)
      (anisotropicLinearEquiv.symm second) ≤ (1 : Real) * dist first second
  simpa [dist_eq_norm] using anisotropic_inverse_norm_le_one (first - second)

def anisotropicControlledEquiv : ControlledEquiv AmbientPlane AmbientPlane where
  toHomeomorph := anisotropicContinuousLinearEquiv.toHomeomorph
  forwardConstant := 2
  inverseConstant := 1
  forward_lipschitz := anisotropic_forward_lipschitz
  inverse_lipschitz := anisotropic_inverse_lipschitz

def ellipseRegion : Set AmbientPlane :=
  anisotropicLinearEquiv '' identityRegion

def ellipseInterface : Set AmbientPlane :=
  anisotropicLinearEquiv '' identityInterface

theorem mem_identityInterface_iff_norm_sq (point : AmbientPlane) :
    point ∈ identityInterface ↔ ‖point‖ ^ 2 = 2 := by
  have hRadiusNonnegative : 0 ≤ targetRadius := by
    unfold targetRadius
    positivity
  constructor
  · intro hPoint
    have hNorm : ‖point‖ = targetRadius := by
      change dist point 0 = targetRadius at hPoint
      simpa [dist_eq_norm] using hPoint
    nlinarith [targetRadius_sq]
  · intro hSquared
    have hNormNonnegative : 0 ≤ ‖point‖ := norm_nonneg _
    have hNorm : ‖point‖ = targetRadius := by
      nlinarith [targetRadius_sq]
    change dist point 0 = targetRadius
    simpa [dist_eq_norm] using hNorm

theorem mem_ellipseInterface_iff (point : AmbientPlane) :
    point ∈ ellipseInterface ↔
      point 0 ^ 2 / 4 + point 1 ^ 2 = 2 := by
  constructor
  · rintro ⟨source, hSource, rfl⟩
    have hSourceSquared := (mem_identityInterface_iff_norm_sq source).mp hSource
    rw [ambient_norm_sq_eq_coordinates] at hSourceSquared
    simp
    nlinarith
  · intro hEllipse
    refine ⟨anisotropicLinearEquiv.symm point, ?_,
      anisotropicLinearEquiv.apply_symm_apply point⟩
    apply (mem_identityInterface_iff_norm_sq _).mpr
    rw [anisotropic_inverse_norm_sq_eq]
    exact hEllipse

def ellipseComputableBoundaryModel
    (anchors : forall n : Nat, ContourState (n + 1)) :
    ComputableBoundaryModel AmbientPlane :=
  transportComputableBoundaryModel anisotropicControlledEquiv
    (radialComputableBoundaryModel anchors)

theorem ellipse_model_interface_eq
    (anchors : forall n : Nat, ContourState (n + 1)) :
    (ellipseComputableBoundaryModel anchors).interface = ellipseInterface := by
  rfl

theorem ellipse_actual_frontier_equation
    (anchors : forall n : Nat, ContourState (n + 1)) :
    frontier (ellipseComputableBoundaryModel anchors).inside =
      {point : AmbientPlane | point 0 ^ 2 / 4 + point 1 ^ 2 = 2} := by
  rw [(ellipseComputableBoundaryModel anchors).interface_is_frontier]
  rw [ellipse_model_interface_eq]
  ext point
  exact mem_ellipseInterface_iff point

theorem ellipse_model_error_le
    (anchors : forall n : Nat, ContourState (n + 1)) (n : Nat) :
    Metric.hausdorffDist
      ((ellipseComputableBoundaryModel anchors).approximation.carrier n)
      (ellipseComputableBoundaryModel anchors).interface ≤
    2 * (radialComputableBoundaryModel anchors).approximation.envelope n := by
  simpa [ellipseComputableBoundaryModel, anisotropicControlledEquiv] using
    transported_model_error_le anisotropicControlledEquiv
      (radialComputableBoundaryModel anchors) n

theorem ellipse_model_converges_to_actual_frontier
    (anchors : forall n : Nat, ContourState (n + 1)) :
    Tendsto
      (fun n => Metric.hausdorffDist
        ((ellipseComputableBoundaryModel anchors).approximation.carrier n)
        (frontier (ellipseComputableBoundaryModel anchors).inside))
      atTop (nhds 0) := by
  exact transported_model_converges_to_actual_frontier
    anisotropicControlledEquiv (radialComputableBoundaryModel anchors)

end
end AnisotropicEllipseChamber
end BoundaryOfSelf
