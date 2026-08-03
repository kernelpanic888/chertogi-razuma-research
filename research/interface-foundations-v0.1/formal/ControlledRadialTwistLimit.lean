import CompactRadialTwistHomeomorphism
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace BoundaryOfSelf
namespace ControlledRadialTwistLimit

noncomputable section

open Filter
open Set
open StandardHausdorffMetricBridge
open BoundarySeparationInvariant
open AnisotropicEllipseChamber
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport
open ControlledEquivComposition
open FiniteControlledChain
open TwoSidedLimitHomeomorph
open CompactTentHomeomorphism
open SummableCompactTentWitness
open CompactRadialTwistHomeomorphism

def quarterTurn (point : AmbientPlane) : AmbientPlane :=
  planeEmbedding { x := -point 1, y := point 0 }

@[simp]
theorem quarterTurn_apply_zero (point : AmbientPlane) :
    quarterTurn point 0 = -point 1 := by
  simp [quarterTurn, planeEmbedding]

@[simp]
theorem quarterTurn_apply_one (point : AmbientPlane) :
    quarterTurn point 1 = point 0 := by
  simp [quarterTurn, planeEmbedding]

@[simp]
theorem quarterTurn_norm (point : AmbientPlane) :
    ‖quarterTurn point‖ = ‖point‖ := by
  have hSquared : ‖quarterTurn point‖ ^ 2 = ‖point‖ ^ 2 := by
    rw [ambient_norm_sq_eq_coordinates, ambient_norm_sq_eq_coordinates]
    simp [quarterTurn, planeEmbedding]
    ring
  nlinarith [norm_nonneg (quarterTurn point), norm_nonneg point]

theorem rotatePoint_decomposition (angle : Real) (point : AmbientPlane) :
    rotatePoint angle point =
      Real.cos angle • point + Real.sin angle • quarterTurn point := by
  ext i
  fin_cases i <;> simp [rotatePoint, quarterTurn, planeEmbedding] <;> ring

theorem rotatePoint_sub (angle : Real) (first second : AmbientPlane) :
    rotatePoint angle (first - second) =
      rotatePoint angle first - rotatePoint angle second := by
  ext i
  fin_cases i <;> simp [rotatePoint, planeEmbedding] <;> ring

theorem rotatePoint_dist (angle : Real) (first second : AmbientPlane) :
    dist (rotatePoint angle first) (rotatePoint angle second) =
      dist first second := by
  rw [dist_eq_norm, dist_eq_norm, ← rotatePoint_sub, rotatePoint_norm]

theorem rotatePoint_angle_dist_le
    (firstAngle secondAngle : Real) (point : AmbientPlane) :
    dist (rotatePoint firstAngle point) (rotatePoint secondAngle point) <=
      2 * |firstAngle - secondAngle| * ‖point‖ := by
  have hDifference :
      rotatePoint firstAngle point - rotatePoint secondAngle point =
        (Real.cos firstAngle - Real.cos secondAngle) • point +
        (Real.sin firstAngle - Real.sin secondAngle) • quarterTurn point := by
    rw [rotatePoint_decomposition, rotatePoint_decomposition]
    ext i
    fin_cases i <;> simp <;> ring
  rw [dist_eq_norm, hDifference]
  calc
    ‖(Real.cos firstAngle - Real.cos secondAngle) • point +
        (Real.sin firstAngle - Real.sin secondAngle) • quarterTurn point‖ <=
        ‖(Real.cos firstAngle - Real.cos secondAngle) • point‖ +
          ‖(Real.sin firstAngle - Real.sin secondAngle) • quarterTurn point‖ :=
      norm_add_le _ _
    _ = |Real.cos firstAngle - Real.cos secondAngle| * ‖point‖ +
        |Real.sin firstAngle - Real.sin secondAngle| * ‖point‖ := by
      simp [norm_smul, Real.norm_eq_abs]
    _ <= |firstAngle - secondAngle| * ‖point‖ +
        |firstAngle - secondAngle| * ‖point‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (Real.abs_cos_sub_cos_le firstAngle secondAngle) (norm_nonneg point))
        (mul_le_mul_of_nonneg_right
          (Real.abs_sin_sub_sin_le firstAngle secondAngle) (norm_nonneg point))
    _ = 2 * |firstAngle - secondAngle| * ‖point‖ := by ring

theorem radialTwistAngle_abs_sub_le
    (amplitude : Real) (first second : AmbientPlane) :
    |radialTwistAngle amplitude first - radialTwistAngle amplitude second| <=
      |amplitude| * dist first second := by
  have hBump :
      |tentBump ‖first‖ - tentBump ‖second‖| <= dist first second := by
    calc
      |tentBump ‖first‖ - tentBump ‖second‖| =
          dist (tentBump ‖first‖) (tentBump ‖second‖) := by
        rw [Real.dist_eq]
      _ <= dist ‖first‖ ‖second‖ := by
        simpa using tentBump_lipschitz.dist_le_mul ‖first‖ ‖second‖
      _ <= dist first second := dist_norm_norm_le first second
  rw [radialTwistAngle, radialTwistAngle, ← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left hBump (abs_nonneg amplitude)

theorem radialTwistMap_dist_le_of_norm_le
    (amplitude : Real) {first second : AmbientPlane}
    (hNormOrder : ‖first‖ <= ‖second‖) :
    dist (radialTwistMap amplitude first) (radialTwistMap amplitude second) <=
      (1 + 2 * |amplitude|) * dist first second := by
  by_cases hUnit : ‖first‖ <= 1
  · have hAngle := radialTwistAngle_abs_sub_le amplitude first second
    have hAngleRadius :
        |radialTwistAngle amplitude first - radialTwistAngle amplitude second| *
            ‖first‖ <=
          (|amplitude| * dist first second) * 1 :=
      mul_le_mul hAngle hUnit (norm_nonneg first)
        (mul_nonneg (abs_nonneg amplitude) dist_nonneg)
    calc
      dist (radialTwistMap amplitude first) (radialTwistMap amplitude second) <=
          dist (radialTwistMap amplitude first)
              (rotatePoint (radialTwistAngle amplitude second) first) +
            dist (rotatePoint (radialTwistAngle amplitude second) first)
              (radialTwistMap amplitude second) :=
        dist_triangle _ _ _
      _ <= 2 *
            |radialTwistAngle amplitude first - radialTwistAngle amplitude second| *
              ‖first‖ + dist first second := by
        exact add_le_add
          (rotatePoint_angle_dist_le
            (radialTwistAngle amplitude first)
            (radialTwistAngle amplitude second) first)
          (le_of_eq (rotatePoint_dist
            (radialTwistAngle amplitude second) first second))
      _ <= 2 * (|amplitude| * dist first second) * 1 + dist first second := by
        have hScaled := mul_le_mul_of_nonneg_left hAngleRadius
          (show (0 : Real) <= 2 by norm_num)
        exact add_le_add (by simpa [mul_assoc] using hScaled) (le_refl _)
      _ = (1 + 2 * |amplitude|) * dist first second := by ring
  · have hFirst : 1 <= ‖first‖ := le_of_lt (lt_of_not_ge hUnit)
    have hSecond : 1 <= ‖second‖ := hFirst.trans hNormOrder
    have hFirstBump : tentBump ‖first‖ = 0 :=
      tentBump_eq_zero_of_abs_ge_one (by
        simpa [abs_of_nonneg (norm_nonneg first)] using hFirst)
    have hSecondBump : tentBump ‖second‖ = 0 :=
      tentBump_eq_zero_of_abs_ge_one (by
        simpa [abs_of_nonneg (norm_nonneg second)] using hSecond)
    simp [radialTwistMap, radialTwistAngle, hFirstBump, hSecondBump]
    exact le_mul_of_one_le_left dist_nonneg
      (by nlinarith [abs_nonneg amplitude])

theorem radialTwistMap_dist_le
    (amplitude : Real) (first second : AmbientPlane) :
    dist (radialTwistMap amplitude first) (radialTwistMap amplitude second) <=
      (1 + 2 * |amplitude|) * dist first second := by
  rcases le_total ‖first‖ ‖second‖ with hOrder | hOrder
  · exact radialTwistMap_dist_le_of_norm_le amplitude hOrder
  · simpa [dist_comm] using
      radialTwistMap_dist_le_of_norm_le amplitude
        (first := second) (second := first) hOrder

def radialTwistConstant (amplitude : Real) : NNReal :=
  (1 + 2 * |amplitude|).toNNReal

@[simp]
theorem radialTwistConstant_coe (amplitude : Real) :
    (radialTwistConstant amplitude : Real) = 1 + 2 * |amplitude| := by
  rw [radialTwistConstant, Real.coe_toNNReal]
  positivity

theorem radialTwistMap_lipschitz (amplitude : Real) :
    LipschitzWith (radialTwistConstant amplitude) (radialTwistMap amplitude) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [radialTwistConstant_coe]
  exact radialTwistMap_dist_le amplitude first second

def controlledRadialTwist (amplitude : Real) :
    ControlledEquiv AmbientPlane AmbientPlane where
  toHomeomorph := radialTwistHomeomorph amplitude
  forwardConstant := radialTwistConstant amplitude
  inverseConstant := radialTwistConstant amplitude
  forward_lipschitz := radialTwistMap_lipschitz amplitude
  inverse_lipschitz := by
    change LipschitzWith (radialTwistConstant amplitude)
      (radialTwistMap (-amplitude))
    simpa [radialTwistConstant, abs_neg] using radialTwistMap_lipschitz (-amplitude)

@[simp]
theorem controlledRadialTwist_apply
    (amplitude : Real) (point : AmbientPlane) :
    controlledRadialTwist amplitude point = radialTwistMap amplitude point := rfl

theorem radialTwistMap_add
    (firstAmplitude secondAmplitude : Real) (point : AmbientPlane) :
    radialTwistMap firstAmplitude (radialTwistMap secondAmplitude point) =
      radialTwistMap (firstAmplitude + secondAmplitude) point := by
  rw [radialTwistMap, radialTwistAngle, radialTwistMap_norm]
  rw [radialTwistMap, radialTwistAngle, rotatePoint_add]
  congr 1
  simp [radialTwistAngle]
  ring

def radialStepAmplitude (n : Nat) : Real :=
  localAmplitude (n + 1) - localAmplitude n

theorem radialStepAmplitude_nonnegative (n : Nat) :
    0 <= radialStepAmplitude n := by
  exact sub_nonneg.mpr (localAmplitude_mono_step n)

def radialTwistSequence (n : Nat) : ControlledEquiv AmbientPlane AmbientPlane :=
  controlledRadialTwist (radialStepAmplitude n)

def limitRadialTwist : AmbientPlane ≃ₜ AmbientPlane :=
  radialTwistHomeomorph (1 / 2)

theorem prefix_radialTwist_apply (n : Nat) (point : AmbientPlane) :
    prefixControlledEquiv radialTwistSequence n point =
      radialTwistHomeomorph (localAmplitude n) point := by
  induction n with
  | zero =>
      simp [prefixControlledEquiv, localAmplitude_zero,
        radialTwistHomeomorph_apply, radialTwistMap, radialTwistAngle]
  | succ n inductionHypothesis =>
      change radialTwistSequence n
          (prefixControlledEquiv radialTwistSequence n point) =
        radialTwistHomeomorph (localAmplitude (n + 1)) point
      rw [inductionHypothesis]
      change radialTwistMap (radialStepAmplitude n)
          (radialTwistMap (localAmplitude n) point) =
        radialTwistMap (localAmplitude (n + 1)) point
      rw [radialTwistMap_add]
      congr 2
      simp [radialStepAmplitude]

theorem prefix_radialTwist_inverse_apply (n : Nat) (point : AmbientPlane) :
    (prefixControlledEquiv radialTwistSequence n).toHomeomorph.symm point =
      radialTwistHomeomorph (-localAmplitude n) point := by
  apply (prefixControlledEquiv radialTwistSequence n).toHomeomorph.injective
  rw [(prefixControlledEquiv radialTwistSequence n).toHomeomorph.apply_symm_apply]
  rw [prefix_radialTwist_apply]
  change point = radialTwistMap (localAmplitude n)
      (radialTwistMap (-localAmplitude n) point)
  exact (radialTwistMap_comp_neg (localAmplitude n) point).symm

theorem radialTwistSequence_forwardConstant_coe (n : Nat) :
    ((radialTwistSequence n).forwardConstant : Real) =
      1 + 2 * radialStepAmplitude n := by
  change (radialTwistConstant (radialStepAmplitude n) : Real) =
    1 + 2 * radialStepAmplitude n
  rw [radialTwistConstant_coe,
    abs_of_nonneg (radialStepAmplitude_nonnegative n)]

theorem radialTwistSequence_inverseConstant_coe (n : Nat) :
    ((radialTwistSequence n).inverseConstant : Real) =
      1 + 2 * radialStepAmplitude n := by
  change (radialTwistConstant (radialStepAmplitude n) : Real) =
    1 + 2 * radialStepAmplitude n
  rw [radialTwistConstant_coe,
    abs_of_nonneg (radialStepAmplitude_nonnegative n)]

theorem prefix_radialTwist_forward_exp_bound (n : Nat) :
    ((prefixControlledEquiv radialTwistSequence n).forwardConstant : Real) <=
      Real.exp (2 * localAmplitude n) := by
  induction n with
  | zero =>
      change (1 : Real) <= Real.exp (2 * localAmplitude 0)
      simp [localAmplitude_zero]
  | succ n inductionHypothesis =>
      change ((radialTwistSequence n).forwardConstant : Real) *
          ((prefixControlledEquiv radialTwistSequence n).forwardConstant : Real) <=
        Real.exp (2 * localAmplitude (n + 1))
      rw [radialTwistSequence_forwardConstant_coe]
      have hExp : 1 + 2 * radialStepAmplitude n <=
          Real.exp (2 * radialStepAmplitude n) := by
        simpa [add_comm] using Real.add_one_le_exp (2 * radialStepAmplitude n)
      calc
        (1 + 2 * radialStepAmplitude n) *
            ((prefixControlledEquiv radialTwistSequence n).forwardConstant : Real) <=
            Real.exp (2 * radialStepAmplitude n) *
              Real.exp (2 * localAmplitude n) :=
          mul_le_mul hExp inductionHypothesis (NNReal.coe_nonneg _)
            (Real.exp_nonneg _)
        _ = Real.exp
            (2 * radialStepAmplitude n + 2 * localAmplitude n) := by
          rw [Real.exp_add]
        _ = Real.exp (2 * localAmplitude (n + 1)) := by
          congr 1
          simp [radialStepAmplitude]
          ring

theorem prefix_radialTwist_inverse_exp_bound (n : Nat) :
    ((prefixControlledEquiv radialTwistSequence n).inverseConstant : Real) <=
      Real.exp (2 * localAmplitude n) := by
  induction n with
  | zero =>
      change (1 : Real) <= Real.exp (2 * localAmplitude 0)
      simp [localAmplitude_zero]
  | succ n inductionHypothesis =>
      change ((prefixControlledEquiv radialTwistSequence n).inverseConstant : Real) *
          ((radialTwistSequence n).inverseConstant : Real) <=
        Real.exp (2 * localAmplitude (n + 1))
      rw [radialTwistSequence_inverseConstant_coe]
      have hExp : 1 + 2 * radialStepAmplitude n <=
          Real.exp (2 * radialStepAmplitude n) := by
        simpa [add_comm] using Real.add_one_le_exp (2 * radialStepAmplitude n)
      calc
        ((prefixControlledEquiv radialTwistSequence n).inverseConstant : Real) *
            (1 + 2 * radialStepAmplitude n) <=
            Real.exp (2 * localAmplitude n) *
              Real.exp (2 * radialStepAmplitude n) :=
          mul_le_mul inductionHypothesis hExp
            (by nlinarith [radialStepAmplitude_nonnegative n])
            (Real.exp_nonneg _)
        _ = Real.exp
            (2 * localAmplitude n + 2 * radialStepAmplitude n) := by
          rw [Real.exp_add]
        _ = Real.exp (2 * localAmplitude (n + 1)) := by
          congr 1
          simp [radialStepAmplitude]
          ring

theorem prefix_radialTwist_forward_bound (n : Nat) :
    ((prefixControlledEquiv radialTwistSequence n).forwardConstant : Real) <=
      Real.exp 1 := by
  exact (prefix_radialTwist_forward_exp_bound n).trans
    (Real.exp_le_exp.mpr (by linarith [localAmplitude_le_half n]))

theorem prefix_radialTwist_inverse_bound (n : Nat) :
    ((prefixControlledEquiv radialTwistSequence n).inverseConstant : Real) <=
      Real.exp 1 := by
  exact (prefix_radialTwist_inverse_exp_bound n).trans
    (Real.exp_le_exp.mpr (by linarith [localAmplitude_le_half n]))

theorem radialTwistMap_amplitude_dist_le
    (firstAmplitude secondAmplitude : Real) (point : AmbientPlane) :
    dist (radialTwistMap firstAmplitude point)
        (radialTwistMap secondAmplitude point) <=
      2 * dist firstAmplitude secondAmplitude := by
  by_cases hUnit : ‖point‖ <= 1
  · have hBumpNonnegative := tentBump_nonnegative ‖point‖
    have hBumpOne := tentBump_le_one ‖point‖
    have hAngle :
        |radialTwistAngle firstAmplitude point -
            radialTwistAngle secondAmplitude point| <=
          dist firstAmplitude secondAmplitude := by
      rw [radialTwistAngle, radialTwistAngle, ← sub_mul, abs_mul]
      rw [abs_of_nonneg hBumpNonnegative]
      calc
        |firstAmplitude - secondAmplitude| * tentBump ‖point‖ <=
            |firstAmplitude - secondAmplitude| * 1 :=
          mul_le_mul_of_nonneg_left hBumpOne (abs_nonneg _)
        _ = dist firstAmplitude secondAmplitude := by
          rw [Real.dist_eq, mul_one]
    have hAngleRadius :
        |radialTwistAngle firstAmplitude point -
            radialTwistAngle secondAmplitude point| * ‖point‖ <=
          dist firstAmplitude secondAmplitude * 1 :=
      mul_le_mul hAngle hUnit (norm_nonneg point) dist_nonneg
    calc
      dist (radialTwistMap firstAmplitude point)
          (radialTwistMap secondAmplitude point) <=
          2 * |radialTwistAngle firstAmplitude point -
            radialTwistAngle secondAmplitude point| * ‖point‖ :=
        rotatePoint_angle_dist_le _ _ _
      _ <= 2 * (dist firstAmplitude secondAmplitude * 1) :=
        by
          have hScaled := mul_le_mul_of_nonneg_left hAngleRadius
            (show (0 : Real) <= 2 by norm_num)
          simpa [mul_assoc] using hScaled
      _ = 2 * dist firstAmplitude secondAmplitude := by ring
  · have hNorm : 1 <= ‖point‖ := le_of_lt (lt_of_not_ge hUnit)
    have hBump : tentBump ‖point‖ = 0 :=
      tentBump_eq_zero_of_abs_ge_one (by
        simpa [abs_of_nonneg (norm_nonneg point)] using hNorm)
    simp [radialTwistMap, radialTwistAngle, hBump]

theorem prefix_radialTwists_tendsto_uniformly :
    TendstoUniformlyOn
      (fun n point => prefixControlledEquiv radialTwistSequence n point)
      limitRadialTwist atTop univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hEpsilon
  have hAmplitude := localAmplitude_tendsto_half
  rw [Metric.tendsto_atTop] at hAmplitude
  obtain ⟨N, hN⟩ := hAmplitude (epsilon / 2) (half_pos hEpsilon)
  refine eventually_atTop.2 ⟨N, fun n hn point _ => ?_⟩
  rw [prefix_radialTwist_apply]
  change dist (radialTwistMap (1 / 2) point)
      (radialTwistMap (localAmplitude n) point) < epsilon
  calc
    dist (radialTwistMap (1 / 2) point)
        (radialTwistMap (localAmplitude n) point) <=
        2 * dist (1 / 2 : Real) (localAmplitude n) :=
      radialTwistMap_amplitude_dist_le _ _ _
    _ = 2 * dist (localAmplitude n) (1 / 2 : Real) := by rw [dist_comm]
    _ < 2 * (epsilon / 2) :=
      mul_lt_mul_of_pos_left (hN n hn) (by norm_num)
    _ = epsilon := by ring

theorem inverse_prefix_radialTwists_tendsto_uniformly :
    TendstoUniformlyOn
      (fun n point =>
        (prefixControlledEquiv radialTwistSequence n).toHomeomorph.symm point)
      limitRadialTwist.symm atTop univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hEpsilon
  have hAmplitude := localAmplitude_tendsto_half
  rw [Metric.tendsto_atTop] at hAmplitude
  obtain ⟨N, hN⟩ := hAmplitude (epsilon / 2) (half_pos hEpsilon)
  refine eventually_atTop.2 ⟨N, fun n hn point _ => ?_⟩
  rw [prefix_radialTwist_inverse_apply]
  change dist (radialTwistMap (-(1 / 2 : Real)) point)
      (radialTwistMap (-localAmplitude n) point) < epsilon
  calc
    dist (radialTwistMap (-(1 / 2 : Real)) point)
        (radialTwistMap (-localAmplitude n) point) <=
        2 * dist (-(1 / 2 : Real)) (-localAmplitude n) :=
      radialTwistMap_amplitude_dist_le _ _ _
    _ = 2 * dist (localAmplitude n) (1 / 2 : Real) := by
      rw [Real.dist_eq, Real.dist_eq]
      congr 1
      ring_nf
    _ < 2 * (epsilon / 2) :=
      mul_lt_mul_of_pos_left (hN n hn) (by norm_num)
    _ = epsilon := by ring

theorem forward_radialTwist_prefixes_uniformCauchy :
    UniformCauchySeqOn
      (fun n point => prefixControlledEquiv radialTwistSequence n point)
      atTop univ :=
  prefix_radialTwists_tendsto_uniformly.uniformCauchySeqOn

theorem inverse_radialTwist_prefixes_uniformCauchy :
    UniformCauchySeqOn
      (fun n point =>
        (prefixControlledEquiv radialTwistSequence n).toHomeomorph.symm point)
      atTop univ :=
  inverse_prefix_radialTwists_tendsto_uniformly.uniformCauchySeqOn

theorem prefix_radialTwist_identity_outside
    (n : Nat) {point : AmbientPlane} (hPoint : point ∉ radialTwistSupport) :
    prefixControlledEquiv radialTwistSequence n point = point := by
  rw [prefix_radialTwist_apply]
  exact radialTwist_identity_outside (localAmplitude n) hPoint

theorem limit_radialTwist_identity_outside
    {point : AmbientPlane} (hPoint : point ∉ radialTwistSupport) :
    limitRadialTwist point = point := by
  exact radialTwist_identity_outside (1 / 2) hPoint

theorem exists_compact_radialTwist_limit
    (model : ComputableBoundaryModel AmbientPlane) :
    ∃ limitHomeomorph : AmbientPlane ≃ₜ AmbientPlane,
      limitHomeomorph = limitRadialTwist ∧
      frontier (limitHomeomorph '' model.inside) =
        limitHomeomorph '' model.interface ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          (prefixComputableBoundaryModel radialTwistSequence n model).interface
          (limitHomeomorph '' model.interface))
        atTop (nhds 0) ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          ((prefixComputableBoundaryModel radialTwistSequence n model).approximation.carrier n)
          (limitHomeomorph '' model.interface))
        atTop (nhds 0) := by
  obtain ⟨limitHomeomorph, hForwardLimit, _hInverseLimit,
    hFrontier, hMoving, hComputed⟩ :=
    exists_limit_homeomorph_and_actual_frontier
      radialTwistSequence model forward_radialTwist_prefixes_uniformCauchy
      inverse_radialTwist_prefixes_uniformCauchy (Real.exp 1) (Real.exp 1)
      prefix_radialTwist_forward_bound prefix_radialTwist_inverse_bound
  have hExact : limitHomeomorph = limitRadialTwist := by
    apply Homeomorph.ext
    intro point
    exact tendsto_nhds_unique
      (hForwardLimit.tendsto_at (mem_univ point))
      (prefix_radialTwists_tendsto_uniformly.tendsto_at (mem_univ point))
  exact ⟨limitHomeomorph, hExact, hFrontier, hMoving, hComputed⟩

end
end ControlledRadialTwistLimit
end BoundaryOfSelf
