import AnisotropicEllipseChamber

namespace BoundaryOfSelf
namespace DiagonalEllipseFamily

noncomputable section

open Filter
open StandardHausdorffMetricBridge
open ConcreteRadialContourTraversal
open BoundarySeparationInvariant
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport
open AnisotropicEllipseChamber

/-!
IF-BS-22F-F3 packages every positive diagonal deformation

  F_{a,b}(x,y) = (a x,b y),  a>0, b>0,

as a controlled equivalence. The exact transported frontier is the ellipse
x^2/a^2 + y^2/b^2 = 2. Its approximation error is multiplied by max(a,b).
-/

def diagonalLinearEquiv (a b : Real) (ha : a ≠ 0) (hb : b ≠ 0) :
    AmbientPlane ≃ₗ[Real] AmbientPlane where
  toFun point := planeEmbedding { x := a * point 0, y := b * point 1 }
  invFun point := planeEmbedding { x := point 0 / a, y := point 1 / b }
  left_inv point := by
    ext i
    fin_cases i <;> simp [planeEmbedding] <;> field_simp [ha, hb]
  right_inv point := by
    ext i
    fin_cases i <;> simp [planeEmbedding] <;> field_simp [ha, hb]
  map_add' first second := by
    ext i
    fin_cases i <;> simp [planeEmbedding] <;> ring
  map_smul' scalar point := by
    ext i
    fin_cases i <;> simp [planeEmbedding] <;> ring

@[simp]
theorem diagonal_apply_zero (a b : Real) (ha : a ≠ 0) (hb : b ≠ 0)
    (point : AmbientPlane) :
    diagonalLinearEquiv a b ha hb point 0 = a * point 0 := by
  simp [diagonalLinearEquiv, planeEmbedding]

@[simp]
theorem diagonal_apply_one (a b : Real) (ha : a ≠ 0) (hb : b ≠ 0)
    (point : AmbientPlane) :
    diagonalLinearEquiv a b ha hb point 1 = b * point 1 := by
  simp [diagonalLinearEquiv, planeEmbedding]

@[simp]
theorem diagonal_symm_apply_zero (a b : Real) (ha : a ≠ 0) (hb : b ≠ 0)
    (point : AmbientPlane) :
    (diagonalLinearEquiv a b ha hb).symm point 0 = point 0 / a := by
  simp [diagonalLinearEquiv, planeEmbedding]

@[simp]
theorem diagonal_symm_apply_one (a b : Real) (ha : a ≠ 0) (hb : b ≠ 0)
    (point : AmbientPlane) :
    (diagonalLinearEquiv a b ha hb).symm point 1 = point 1 / b := by
  simp [diagonalLinearEquiv, planeEmbedding]

theorem diagonal_norm_sq_eq (a b : Real) (ha : a ≠ 0) (hb : b ≠ 0)
    (point : AmbientPlane) :
    ‖diagonalLinearEquiv a b ha hb point‖ ^ 2 =
      a ^ 2 * point 0 ^ 2 + b ^ 2 * point 1 ^ 2 := by
  rw [ambient_norm_sq_eq_coordinates]
  simp
  ring

theorem diagonal_inverse_norm_sq_eq (a b : Real) (ha : a ≠ 0) (hb : b ≠ 0)
    (point : AmbientPlane) :
    ‖(diagonalLinearEquiv a b ha hb).symm point‖ ^ 2 =
      a⁻¹ ^ 2 * point 0 ^ 2 + b⁻¹ ^ 2 * point 1 ^ 2 := by
  rw [ambient_norm_sq_eq_coordinates]
  simp [div_eq_mul_inv]
  ring

theorem diagonal_norm_le_max (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (point : AmbientPlane) :
    ‖diagonalLinearEquiv a b ha.ne' hb.ne' point‖ ≤
      max a b * ‖point‖ := by
  have haMax : a ≤ max a b := le_max_left _ _
  have hbMax : b ≤ max a b := le_max_right _ _
  have hMaxNonnegative : 0 ≤ max a b := le_trans ha.le haMax
  have haSquared : a ^ 2 ≤ (max a b) ^ 2 := by nlinarith
  have hbSquared : b ^ 2 ≤ (max a b) ^ 2 := by nlinarith
  have hSquared :
      ‖diagonalLinearEquiv a b ha.ne' hb.ne' point‖ ^ 2 ≤
        (max a b * ‖point‖) ^ 2 := by
    calc
      ‖diagonalLinearEquiv a b ha.ne' hb.ne' point‖ ^ 2 =
          a ^ 2 * point 0 ^ 2 + b ^ 2 * point 1 ^ 2 :=
        diagonal_norm_sq_eq a b ha.ne' hb.ne' point
      _ ≤ (max a b) ^ 2 * point 0 ^ 2 +
          (max a b) ^ 2 * point 1 ^ 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right haSquared (sq_nonneg _))
          (mul_le_mul_of_nonneg_right hbSquared (sq_nonneg _))
      _ = (max a b) ^ 2 * (point 0 ^ 2 + point 1 ^ 2) := by ring
      _ = (max a b) ^ 2 * ‖point‖ ^ 2 := by
        rw [ambient_norm_sq_eq_coordinates]
      _ = (max a b * ‖point‖) ^ 2 := by ring
  have hLeft : 0 ≤ ‖diagonalLinearEquiv a b ha.ne' hb.ne' point‖ := norm_nonneg _
  have hRight : 0 ≤ max a b * ‖point‖ :=
    mul_nonneg hMaxNonnegative (norm_nonneg _)
  nlinarith

theorem diagonal_inverse_norm_le_max (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (point : AmbientPlane) :
    ‖(diagonalLinearEquiv a b ha.ne' hb.ne').symm point‖ ≤
      max a⁻¹ b⁻¹ * ‖point‖ := by
  have haInv : 0 < a⁻¹ := inv_pos.mpr ha
  have hbInv : 0 < b⁻¹ := inv_pos.mpr hb
  have haMax : a⁻¹ ≤ max a⁻¹ b⁻¹ := le_max_left _ _
  have hbMax : b⁻¹ ≤ max a⁻¹ b⁻¹ := le_max_right _ _
  have hMaxNonnegative : 0 ≤ max a⁻¹ b⁻¹ := le_trans haInv.le haMax
  have haSquared : a⁻¹ ^ 2 ≤ (max a⁻¹ b⁻¹) ^ 2 := by nlinarith
  have hbSquared : b⁻¹ ^ 2 ≤ (max a⁻¹ b⁻¹) ^ 2 := by nlinarith
  have hSquared :
      ‖(diagonalLinearEquiv a b ha.ne' hb.ne').symm point‖ ^ 2 ≤
        (max a⁻¹ b⁻¹ * ‖point‖) ^ 2 := by
    calc
      ‖(diagonalLinearEquiv a b ha.ne' hb.ne').symm point‖ ^ 2 =
          a⁻¹ ^ 2 * point 0 ^ 2 + b⁻¹ ^ 2 * point 1 ^ 2 :=
        diagonal_inverse_norm_sq_eq a b ha.ne' hb.ne' point
      _ ≤ (max a⁻¹ b⁻¹) ^ 2 * point 0 ^ 2 +
          (max a⁻¹ b⁻¹) ^ 2 * point 1 ^ 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right haSquared (sq_nonneg _))
          (mul_le_mul_of_nonneg_right hbSquared (sq_nonneg _))
      _ = (max a⁻¹ b⁻¹) ^ 2 * (point 0 ^ 2 + point 1 ^ 2) := by ring
      _ = (max a⁻¹ b⁻¹) ^ 2 * ‖point‖ ^ 2 := by
        rw [ambient_norm_sq_eq_coordinates]
      _ = (max a⁻¹ b⁻¹ * ‖point‖) ^ 2 := by ring
  have hLeft : 0 ≤ ‖(diagonalLinearEquiv a b ha.ne' hb.ne').symm point‖ := norm_nonneg _
  have hRight : 0 ≤ max a⁻¹ b⁻¹ * ‖point‖ :=
    mul_nonneg hMaxNonnegative (norm_nonneg _)
  nlinarith

def diagonalForwardConstant (a b : Real) (ha : 0 < a) : NNReal :=
  ⟨max a b, (ha.trans_le (le_max_left _ _)).le⟩

def diagonalInverseConstant (a b : Real) (ha : 0 < a) : NNReal :=
  ⟨max a⁻¹ b⁻¹, ((inv_pos.mpr ha).trans_le (le_max_left _ _)).le⟩

def diagonalContinuousLinearEquiv (a b : Real) (ha : 0 < a) (hb : 0 < b) :
    AmbientPlane ≃L[Real] AmbientPlane :=
  (diagonalLinearEquiv a b ha.ne' hb.ne').toContinuousLinearEquivOfBounds
    (max a b) (max a⁻¹ b⁻¹)
    (diagonal_norm_le_max a b ha hb)
    (diagonal_inverse_norm_le_max a b ha hb)

theorem diagonal_forward_lipschitz (a b : Real) (ha : 0 < a) (hb : 0 < b) :
    LipschitzWith (diagonalForwardConstant a b ha)
      (diagonalContinuousLinearEquiv a b ha hb) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  change dist (diagonalLinearEquiv a b ha.ne' hb.ne' first)
      (diagonalLinearEquiv a b ha.ne' hb.ne' second) ≤
    max a b * dist first second
  simpa [dist_eq_norm] using diagonal_norm_le_max a b ha hb (first - second)

theorem diagonal_inverse_lipschitz (a b : Real) (ha : 0 < a) (hb : 0 < b) :
    LipschitzWith (diagonalInverseConstant a b ha)
      (diagonalContinuousLinearEquiv a b ha hb).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  change dist ((diagonalLinearEquiv a b ha.ne' hb.ne').symm first)
      ((diagonalLinearEquiv a b ha.ne' hb.ne').symm second) ≤
    max a⁻¹ b⁻¹ * dist first second
  simpa [dist_eq_norm] using diagonal_inverse_norm_le_max a b ha hb (first - second)

def diagonalControlledEquiv (a b : Real) (ha : 0 < a) (hb : 0 < b) :
    ControlledEquiv AmbientPlane AmbientPlane where
  toHomeomorph := (diagonalContinuousLinearEquiv a b ha hb).toHomeomorph
  forwardConstant := diagonalForwardConstant a b ha
  inverseConstant := diagonalInverseConstant a b ha
  forward_lipschitz := diagonal_forward_lipschitz a b ha hb
  inverse_lipschitz := diagonal_inverse_lipschitz a b ha hb

def diagonalEllipseInterface (a b : Real) (ha : 0 < a) (hb : 0 < b) :
    Set AmbientPlane :=
  diagonalLinearEquiv a b ha.ne' hb.ne' '' identityInterface

theorem scaled_square_div_sq (scale coordinate : Real) (hScale : scale ≠ 0) :
    (scale * coordinate) ^ 2 / scale ^ 2 = coordinate ^ 2 := by
  field_simp [hScale]

theorem inv_square_mul_eq_div_square
    (scale coordinate : Real) (hScale : scale ≠ 0) :
    scale⁻¹ ^ 2 * coordinate ^ 2 = coordinate ^ 2 / scale ^ 2 := by
  field_simp [hScale]

theorem mem_diagonalEllipseInterface_iff
    (a b : Real) (ha : 0 < a) (hb : 0 < b) (point : AmbientPlane) :
    point ∈ diagonalEllipseInterface a b ha hb ↔
      point 0 ^ 2 / a ^ 2 + point 1 ^ 2 / b ^ 2 = 2 := by
  constructor
  · rintro ⟨source, hSource, rfl⟩
    have hSourceSquared := (mem_identityInterface_iff_norm_sq source).mp hSource
    rw [ambient_norm_sq_eq_coordinates] at hSourceSquared
    change (a * source 0) ^ 2 / a ^ 2 +
      (b * source 1) ^ 2 / b ^ 2 = 2
    rw [scaled_square_div_sq a (source 0) ha.ne',
      scaled_square_div_sq b (source 1) hb.ne']
    exact hSourceSquared
  · intro hEllipse
    refine ⟨(diagonalLinearEquiv a b ha.ne' hb.ne').symm point, ?_,
      (diagonalLinearEquiv a b ha.ne' hb.ne').apply_symm_apply point⟩
    apply (mem_identityInterface_iff_norm_sq _).mpr
    rw [diagonal_inverse_norm_sq_eq]
    rw [inv_square_mul_eq_div_square a (point 0) ha.ne',
      inv_square_mul_eq_div_square b (point 1) hb.ne']
    exact hEllipse

def diagonalEllipseComputableBoundaryModel
    (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (anchors : forall n : Nat, ContourState (n + 1)) :
    ComputableBoundaryModel AmbientPlane :=
  transportComputableBoundaryModel (diagonalControlledEquiv a b ha hb)
    (radialComputableBoundaryModel anchors)

theorem diagonal_ellipse_interface_eq
    (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (anchors : forall n : Nat, ContourState (n + 1)) :
    (diagonalEllipseComputableBoundaryModel a b ha hb anchors).interface =
      diagonalEllipseInterface a b ha hb := by
  rfl

theorem diagonal_ellipse_actual_frontier_equation
    (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (anchors : forall n : Nat, ContourState (n + 1)) :
    frontier (diagonalEllipseComputableBoundaryModel a b ha hb anchors).inside =
      {point : AmbientPlane |
        point 0 ^ 2 / a ^ 2 + point 1 ^ 2 / b ^ 2 = 2} := by
  rw [(diagonalEllipseComputableBoundaryModel a b ha hb anchors).interface_is_frontier]
  rw [diagonal_ellipse_interface_eq]
  ext point
  exact mem_diagonalEllipseInterface_iff a b ha hb point

theorem diagonal_ellipse_model_error_le
    (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (anchors : forall n : Nat, ContourState (n + 1)) (n : Nat) :
    Metric.hausdorffDist
      ((diagonalEllipseComputableBoundaryModel a b ha hb anchors).approximation.carrier n)
      (diagonalEllipseComputableBoundaryModel a b ha hb anchors).interface ≤
    max a b * (radialComputableBoundaryModel anchors).approximation.envelope n := by
  change Metric.hausdorffDist
      ((diagonalEllipseComputableBoundaryModel a b ha hb anchors).approximation.carrier n)
      (diagonalEllipseComputableBoundaryModel a b ha hb anchors).interface ≤
    ((diagonalForwardConstant a b ha : NNReal) : Real) *
      (radialComputableBoundaryModel anchors).approximation.envelope n
  exact transported_model_error_le (diagonalControlledEquiv a b ha hb)
    (radialComputableBoundaryModel anchors) n

theorem diagonal_ellipse_model_converges_to_actual_frontier
    (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (anchors : forall n : Nat, ContourState (n + 1)) :
    Tendsto
      (fun n => Metric.hausdorffDist
        ((diagonalEllipseComputableBoundaryModel a b ha hb anchors).approximation.carrier n)
        (frontier (diagonalEllipseComputableBoundaryModel a b ha hb anchors).inside))
      atTop (nhds 0) := by
  exact transported_model_converges_to_actual_frontier
    (diagonalControlledEquiv a b ha hb) (radialComputableBoundaryModel anchors)

end
end DiagonalEllipseFamily
end BoundaryOfSelf
