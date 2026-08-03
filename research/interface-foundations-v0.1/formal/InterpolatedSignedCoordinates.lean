import InterpolatedCurvatureResidual

namespace BoundaryOfSelf
namespace InterpolatedSignedCoordinates

open RationalBoundaryLimit
open RefinedCurvedBoundaryGrid
open UniformRadialBoundaryFamily
open InterpolatedBoundaryContour
open InterpolatedCurvatureResidual

/-! IF-BS-22B probe. -/

def centeredX {m : Nat} (p : GridSample m) : Int :=
  (p.x : Int) - (centerCoordinate m : Int)

def centeredY {m : Nat} (p : GridSample m) : Int :=
  (p.y : Int) - (centerCoordinate m : Int)

theorem centered_square (a c : Nat) :
    ((a : Int) - (c : Int)) * ((a : Int) - (c : Int)) =
      ((natDistance a c * natDistance a c : Nat) : Int) := by
  unfold natDistance
  split
  next h =>
    have hcast : ((c - a : Nat) : Int) = (c : Int) - (a : Int) :=
      Int.ofNat_sub h
    have hsigned : (a : Int) - (c : Int) = -((c - a : Nat) : Int) := by
      rw [hcast]
      omega
    rw [Int.natCast_mul, hsigned, Int.neg_mul, Int.mul_neg, Int.neg_neg]
  next h =>
    have hca : c <= a := by omega
    have hcast : ((a - c : Nat) : Int) = (a : Int) - (c : Int) :=
      Int.ofNat_sub hca
    rw [Int.natCast_mul, hcast]

theorem centered_radius {m : Nat} (p : GridSample m) :
    centeredX p * centeredX p + centeredY p * centeredY p =
      (radialNumerator p : Int) := by
  unfold centeredX centeredY radialNumerator xOffset yOffset
  rw [centered_square, centered_square, Int.natCast_add]

private theorem int_successor_difference (a c : Int) :
    (a + 1 - c) - (a - c) = 1 := by omega

private theorem int_predecessor_difference (a c : Int) :
    (a - c) - (a + 1 - c) = -1 := by omega

theorem centered_unit_edge {m : Nat} {p q : GridSample m}
    (h : UnitAdjacent p q) :
    (centeredX q - centeredX p) * (centeredX q - centeredX p) +
      (centeredY q - centeredY p) * (centeredY q - centeredY p) = 1 := by
  rcases h with ⟨hy, hqx | hpx⟩ | ⟨hx, hqy | hpy⟩
  · simp [centeredX, centeredY, hy, hqx, int_successor_difference]
  · simp [centeredX, centeredY, hy, hpx, int_predecessor_difference]
  · simp [centeredX, centeredY, hx, hqy, int_successor_difference]
  · simp [centeredX, centeredY, hx, hpy, int_predecessor_difference]

theorem weighted_square_identity (d n u v : Int) :
    (((d - n) * u + n * v) * ((d - n) * u + n * v)) =
      d * (d - n) * (u * u) + d * n * (v * v) -
        n * (d - n) * ((v - u) * (v - u)) := by
  simp [Int.sub_eq_add_neg, Int.mul_add, Int.mul_neg,
    Int.mul_comm, Int.mul_left_comm,
    Int.add_comm, Int.add_left_comm, Int.add_assoc]
  omega

theorem weighted_vector_square_identity
    (d n ux uy vx vy : Int) :
    (((d - n) * ux + n * vx) * ((d - n) * ux + n * vx)) +
      (((d - n) * uy + n * vy) * ((d - n) * uy + n * vy)) =
    d * (d - n) * (ux * ux + uy * uy) +
      d * n * (vx * vx + vy * vy) -
      n * (d - n) *
        ((vx - ux) * (vx - ux) + (vy - uy) * (vy - uy)) := by
  rw [weighted_square_identity, weighted_square_identity]
  simp only [Int.mul_add]
  omega

theorem interpolation_radius_algebra (d n r : Int) :
    d * (d - n) * r + d * n * (r + d) - n * (d - n) * 1 +
        n * (d - n) =
      d * d * (r + n) := by
  simp [Int.sub_eq_add_neg, Int.mul_add, Int.mul_neg,
    Int.mul_comm, Int.mul_left_comm,
    Int.add_comm, Int.add_left_comm, Int.add_assoc]
  omega

def innerWeight {m : Nat} (edge : CrossingEdge m) : Int :=
  (interpolationDenominator edge : Int) -
    (interpolationNumerator edge : Int)

def outerWeight {m : Nat} (edge : CrossingEdge m) : Int :=
  (interpolationNumerator edge : Int)

def interpolatedXNumerator {m : Nat} (edge : CrossingEdge m) : Int :=
  innerWeight edge * centeredX (innerPoint edge) +
    outerWeight edge * centeredX (outerPoint edge)

def interpolatedYNumerator {m : Nat} (edge : CrossingEdge m) : Int :=
  innerWeight edge * centeredY (innerPoint edge) +
    outerWeight edge * centeredY (outerPoint edge)

structure SignedRationalPoint where
  xNumerator : Int
  yNumerator : Int
  denominator : Nat
  denominator_pos : 0 < denominator

def interpolatedSignedPoint {m : Nat} (hm : 0 < m)
    (edge : CrossingEdge m) : SignedRationalPoint where
  xNumerator := interpolatedXNumerator edge
  yNumerator := interpolatedYNumerator edge
  denominator := interpolationDenominator edge * m
  denominator_pos := Nat.mul_pos (interpolationDenominator_pos edge) hm

def squaredRadiusNumerator (point : SignedRationalPoint) : Int :=
  point.xNumerator * point.xNumerator + point.yNumerator * point.yNumerator

def targetCircleNumerator (point : SignedRationalPoint) : Int :=
  2 * (point.denominator : Int) * (point.denominator : Int)

theorem interpolation_raw_radius_identity {m : Nat} (edge : CrossingEdge m) :
    interpolatedXNumerator edge * interpolatedXNumerator edge +
      interpolatedYNumerator edge * interpolatedYNumerator edge +
      (curvatureResidualNumerator edge : Int) =
    (interpolationDenominator edge * interpolationDenominator edge *
      thresholdNumerator m : Nat) := by
  have hvector := weighted_vector_square_identity
    (interpolationDenominator edge : Int)
    (interpolationNumerator edge : Int)
    (centeredX (innerPoint edge)) (centeredY (innerPoint edge))
    (centeredX (outerPoint edge)) (centeredY (outerPoint edge))
  have hunit :
      (centeredX (outerPoint edge) - centeredX (innerPoint edge)) *
          (centeredX (outerPoint edge) - centeredX (innerPoint edge)) +
        (centeredY (outerPoint edge) - centeredY (innerPoint edge)) *
          (centeredY (outerPoint edge) - centeredY (innerPoint edge)) = 1 :=
    centered_unit_edge (oriented_points_adjacent edge)
  have hinner := centered_radius (innerPoint edge)
  have houter := centered_radius (outerPoint edge)
  have hnle : interpolationNumerator edge <= interpolationDenominator edge :=
    interpolationNumerator_le_denominator edge
  have hdifference :
      radialNumerator (outerPoint edge) =
        radialNumerator (innerPoint edge) + interpolationDenominator edge := by
    have hi := innerPoint_inside edge
    have ho := outerPoint_outside edge
    unfold Inside at hi ho
    unfold interpolationDenominator
    omega
  have hthreshold :
      thresholdNumerator m =
        radialNumerator (innerPoint edge) + interpolationNumerator edge := by
    have hi := innerPoint_inside edge
    unfold Inside at hi
    unfold interpolationNumerator
    omega
  rw [hinner, houter, hunit] at hvector
  dsimp [interpolatedXNumerator, interpolatedYNumerator, innerWeight,
    outerWeight]
  dsimp [curvatureResidualNumerator]
  rw [Int.natCast_sub hnle]
  rw [hvector]
  rw [hdifference, hthreshold]
  simpa [Int.natCast_add] using interpolation_radius_algebra
    (interpolationDenominator edge : Int)
    (interpolationNumerator edge : Int)
    (radialNumerator (innerPoint edge) : Int)

theorem interpolation_squared_radius_deficit_exact {m : Nat} (hm : 0 < m)
    (edge : CrossingEdge m) :
    squaredRadiusNumerator (interpolatedSignedPoint hm edge) +
      (curvatureResidualNumerator edge : Int) =
    targetCircleNumerator (interpolatedSignedPoint hm edge) := by
  rw [show squaredRadiusNumerator (interpolatedSignedPoint hm edge) =
      interpolatedXNumerator edge * interpolatedXNumerator edge +
        interpolatedYNumerator edge * interpolatedYNumerator edge by rfl]
  rw [interpolation_raw_radius_identity]
  unfold targetCircleNumerator interpolatedSignedPoint thresholdNumerator
  rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_mul]
  rw [Int.natCast_mul]
  simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]

end InterpolatedSignedCoordinates
end BoundaryOfSelf
