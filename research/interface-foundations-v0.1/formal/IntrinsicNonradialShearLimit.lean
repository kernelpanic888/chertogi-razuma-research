import NonradialEllipticTwistLimit

namespace BoundaryOfSelf
namespace IntrinsicNonradialShearLimit

noncomputable section

open Filter
open Set
open StandardHausdorffMetricBridge
open BoundarySeparationInvariant
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport
open FiniteControlledChain
open UniformCauchyLimitCarrier
open TwoSidedLimitHomeomorph
open AnisotropicEllipseChamber
open CompactTentHomeomorphism
open SummableCompactTentWitness

def shearKernel (point : AmbientPlane) : Real :=
  tentBump (point 0) * tentBump (point 1)

theorem shearKernel_nonnegative (point : AmbientPlane) :
    0 <= shearKernel point :=
  mul_nonneg (tentBump_nonnegative _) (tentBump_nonnegative _)

theorem shearKernel_le_one (point : AmbientPlane) :
    shearKernel point <= 1 := by
  calc
    shearKernel point <= 1 * 1 :=
      mul_le_mul (tentBump_le_one _) (tentBump_le_one _)
        (tentBump_nonnegative _) (by norm_num)
    _ = 1 := by ring

def verticalDisplacement (amplitude : Real) (point : AmbientPlane) : AmbientPlane :=
  planeEmbedding { x := 0, y := amplitude * shearKernel point }

def intrinsicShearMap (amplitude : Real) (point : AmbientPlane) : AmbientPlane :=
  planeEmbedding
    { x := point 0
      y := point 1 + amplitude * shearKernel point }

@[simp]
theorem intrinsicShearMap_apply_zero
    (amplitude : Real) (point : AmbientPlane) :
    intrinsicShearMap amplitude point 0 = point 0 := by
  simp [intrinsicShearMap, planeEmbedding]

@[simp]
theorem intrinsicShearMap_apply_one
    (amplitude : Real) (point : AmbientPlane) :
    intrinsicShearMap amplitude point 1 =
      tentMap (amplitude * tentBump (point 0)) (point 1) := by
  simp [intrinsicShearMap, shearKernel, tentMap, planeEmbedding]
  ring

theorem intrinsicShearMap_eq_add_displacement
    (amplitude : Real) (point : AmbientPlane) :
    intrinsicShearMap amplitude point =
      point + verticalDisplacement amplitude point := by
  ext i
  fin_cases i <;>
    simp [intrinsicShearMap, verticalDisplacement, planeEmbedding]

theorem verticalVector_norm (value : Real) :
    ‖planeEmbedding { x := 0, y := value }‖ = |value| := by
  have hSquared := ambient_norm_sq_eq_coordinates
    (planeEmbedding { x := 0, y := value })
  simp [planeEmbedding] at hSquared
  change ‖!₂[(0 : Real), value]‖ = |value|
  nlinarith [norm_nonneg (!₂[(0 : Real), value] : AmbientPlane), abs_nonneg value,
    sq_abs value]

theorem abs_zero_coordinate_sub_le_dist
    (first second : AmbientPlane) :
    |first 0 - second 0| <= dist first second := by
  simpa [Real.dist_eq] using PiLp.dist_apply_le first second 0

theorem abs_one_coordinate_sub_le_dist
    (first second : AmbientPlane) :
    |first 1 - second 1| <= dist first second := by
  simpa [Real.dist_eq] using PiLp.dist_apply_le first second 1

theorem shearKernel_abs_sub_le
    (first second : AmbientPlane) :
    |shearKernel first - shearKernel second| <= 2 * dist first second := by
  have hZeroBump :
      |tentBump (first 0) - tentBump (second 0)| <=
        |first 0 - second 0| := by
    simpa [Real.dist_eq] using
      tentBump_lipschitz.dist_le_mul (first 0) (second 0)
  have hOneBump :
      |tentBump (first 1) - tentBump (second 1)| <=
        |first 1 - second 1| := by
    simpa [Real.dist_eq] using
      tentBump_lipschitz.dist_le_mul (first 1) (second 1)
  have hRewrite :
      shearKernel first - shearKernel second =
        (tentBump (first 0) - tentBump (second 0)) * tentBump (first 1) +
        tentBump (second 0) *
          (tentBump (first 1) - tentBump (second 1)) := by
    simp [shearKernel]
    ring
  rw [hRewrite]
  calc
    |(tentBump (first 0) - tentBump (second 0)) * tentBump (first 1) +
        tentBump (second 0) *
          (tentBump (first 1) - tentBump (second 1))| <=
        |(tentBump (first 0) - tentBump (second 0)) * tentBump (first 1)| +
        |tentBump (second 0) *
          (tentBump (first 1) - tentBump (second 1))| := abs_add_le _ _
    _ = |tentBump (first 0) - tentBump (second 0)| * tentBump (first 1) +
        tentBump (second 0) *
          |tentBump (first 1) - tentBump (second 1)| := by
      rw [abs_mul, abs_mul,
        abs_of_nonneg (tentBump_nonnegative (first 1)),
        abs_of_nonneg (tentBump_nonnegative (second 0))]
    _ <= |first 0 - second 0| + |first 1 - second 1| := by
      apply add_le_add
      · calc
          |tentBump (first 0) - tentBump (second 0)| * tentBump (first 1) <=
              |first 0 - second 0| * 1 :=
            mul_le_mul hZeroBump (tentBump_le_one _)
              (tentBump_nonnegative _) (abs_nonneg _)
          _ = |first 0 - second 0| := by ring
      · calc
          tentBump (second 0) *
              |tentBump (first 1) - tentBump (second 1)| <=
              1 * |first 1 - second 1| :=
            mul_le_mul (tentBump_le_one _) hOneBump
              (abs_nonneg _) (by norm_num)
          _ = |first 1 - second 1| := by ring
    _ <= dist first second + dist first second :=
      add_le_add (abs_zero_coordinate_sub_le_dist first second)
        (abs_one_coordinate_sub_le_dist first second)
    _ = 2 * dist first second := by ring

theorem verticalDisplacement_dist
    (amplitude : Real) (first second : AmbientPlane) :
    dist (verticalDisplacement amplitude first)
        (verticalDisplacement amplitude second) =
      |amplitude| * |shearKernel first - shearKernel second| := by
  rw [dist_eq_norm]
  have hDifference :
      verticalDisplacement amplitude first - verticalDisplacement amplitude second =
        planeEmbedding
          { x := 0
            y := amplitude * (shearKernel first - shearKernel second) } := by
    ext i
    fin_cases i <;>
      simp [verticalDisplacement, planeEmbedding] <;> ring
  rw [hDifference, verticalVector_norm, abs_mul]

theorem verticalDisplacement_dist_le
    (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (first second : AmbientPlane) :
    dist (verticalDisplacement amplitude first)
        (verticalDisplacement amplitude second) <=
      2 * amplitude * dist first second := by
  rw [verticalDisplacement_dist, abs_of_nonneg hAmplitude]
  have hKernel := shearKernel_abs_sub_le first second
  calc
    amplitude * |shearKernel first - shearKernel second| <=
        amplitude * (2 * dist first second) :=
      mul_le_mul_of_nonneg_left hKernel hAmplitude
    _ = 2 * amplitude * dist first second := by ring

theorem intrinsicShearMap_dist_le
    (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (first second : AmbientPlane) :
    dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second) <=
      (1 + 2 * amplitude) * dist first second := by
  rw [intrinsicShearMap_eq_add_displacement,
    intrinsicShearMap_eq_add_displacement]
  have hDifference :
      (first + verticalDisplacement amplitude first) -
          (second + verticalDisplacement amplitude second) =
        (first - second) +
          (verticalDisplacement amplitude first -
            verticalDisplacement amplitude second) := by abel
  rw [dist_eq_norm, hDifference]
  calc
    ‖(first - second) +
        (verticalDisplacement amplitude first -
          verticalDisplacement amplitude second)‖ <=
        ‖first - second‖ +
          ‖verticalDisplacement amplitude first -
            verticalDisplacement amplitude second‖ := norm_add_le _ _
    _ = dist first second +
        dist (verticalDisplacement amplitude first)
          (verticalDisplacement amplitude second) := by
      simp [dist_eq_norm]
    _ <= dist first second + 2 * amplitude * dist first second :=
      by
        linarith [verticalDisplacement_dist_le amplitude hAmplitude first second]
    _ = (1 + 2 * amplitude) * dist first second := by ring

theorem intrinsicShearMap_colipschitz
    (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (first second : AmbientPlane) :
    (1 - 2 * amplitude) * dist first second <=
      dist (intrinsicShearMap amplitude first)
        (intrinsicShearMap amplitude second) := by
  have hIdentity :
      first - second =
        (intrinsicShearMap amplitude first - intrinsicShearMap amplitude second) -
          (verticalDisplacement amplitude first -
            verticalDisplacement amplitude second) := by
    rw [intrinsicShearMap_eq_add_displacement,
      intrinsicShearMap_eq_add_displacement]
    abel
  have hTriangle :
      dist first second <=
        dist (intrinsicShearMap amplitude first)
            (intrinsicShearMap amplitude second) +
          dist (verticalDisplacement amplitude first)
            (verticalDisplacement amplitude second) := by
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, hIdentity]
    exact norm_sub_le _ _
  have hDisplacement :=
    verticalDisplacement_dist_le amplitude hAmplitude first second
  linarith

def fiberAmplitude (amplitude coordinate : Real) : Real :=
  amplitude * tentBump coordinate

theorem fiberAmplitude_nonnegative
    (amplitude : Real) (hAmplitude : 0 <= amplitude) (coordinate : Real) :
    0 <= fiberAmplitude amplitude coordinate :=
  mul_nonneg hAmplitude (tentBump_nonnegative coordinate)

theorem fiberAmplitude_lt_one
    (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (hQuarter : amplitude <= 1 / 4) (coordinate : Real) :
    fiberAmplitude amplitude coordinate < 1 := by
  have hBound : fiberAmplitude amplitude coordinate <= amplitude := by
    simpa [fiberAmplitude] using
      mul_le_mul_of_nonneg_left (tentBump_le_one coordinate) hAmplitude
  linarith

theorem intrinsicShearMap_injective
    (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (hQuarter : amplitude <= 1 / 4) :
    Function.Injective (intrinsicShearMap amplitude) := by
  intro first second hSame
  have hZero : first 0 = second 0 := by
    simpa using congrArg (fun point : AmbientPlane => point 0) hSame
  have hOneMap := congrArg (fun point : AmbientPlane => point 1) hSame
  simp only [intrinsicShearMap_apply_one] at hOneMap
  rw [hZero] at hOneMap
  have hFiberNonnegative :=
    fiberAmplitude_nonnegative amplitude hAmplitude (second 0)
  have hFiberSmall :=
    fiberAmplitude_lt_one amplitude hAmplitude hQuarter (second 0)
  have hOne : first 1 = second 1 :=
    (tentMap_strictMono (fiberAmplitude amplitude (second 0))
      hFiberNonnegative hFiberSmall).injective hOneMap
  ext i
  fin_cases i
  · exact hZero
  · exact hOne

theorem intrinsicShearMap_surjective
    (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (hQuarter : amplitude <= 1 / 4) :
    Function.Surjective (intrinsicShearMap amplitude) := by
  intro target
  let parameter := fiberAmplitude amplitude (target 0)
  have hParameterNonnegative : 0 <= parameter :=
    fiberAmplitude_nonnegative amplitude hAmplitude (target 0)
  have hParameterSmall : parameter < 1 :=
    fiberAmplitude_lt_one amplitude hAmplitude hQuarter (target 0)
  let sourceY :=
    (tentHomeomorph parameter hParameterNonnegative hParameterSmall).symm (target 1)
  let source : AmbientPlane := planeEmbedding { x := target 0, y := sourceY }
  refine ⟨source, ?_⟩
  ext i
  fin_cases i
  · simp [source, planeEmbedding]
  · have hY : tentMap parameter sourceY = target 1 := by
      rw [← tentHomeomorph_apply]
      exact (tentHomeomorph parameter hParameterNonnegative hParameterSmall).apply_symm_apply
        (target 1)
    simpa [source, planeEmbedding, parameter, fiberAmplitude] using hY

def intrinsicShearEquiv
    (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (hQuarter : amplitude <= 1 / 4) : AmbientPlane ≃ AmbientPlane :=
  Equiv.ofBijective (intrinsicShearMap amplitude)
    ⟨intrinsicShearMap_injective amplitude hAmplitude hQuarter,
      intrinsicShearMap_surjective amplitude hAmplitude hQuarter⟩

@[simp]
theorem intrinsicShearEquiv_apply
    (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (hQuarter : amplitude <= 1 / 4) (point : AmbientPlane) :
    intrinsicShearEquiv amplitude hAmplitude hQuarter point =
      intrinsicShearMap amplitude point := rfl

def intrinsicShearConstant (amplitude : Real) : NNReal :=
  (1 + 4 * amplitude).toNNReal

theorem intrinsicShearConstant_coe
    (amplitude : Real) (hAmplitude : 0 <= amplitude) :
    (intrinsicShearConstant amplitude : Real) = 1 + 4 * amplitude := by
  rw [intrinsicShearConstant, Real.coe_toNNReal]
  linarith

theorem intrinsicShear_forward_lipschitz
    (amplitude : Real) (hAmplitude : 0 <= amplitude) :
    LipschitzWith (intrinsicShearConstant amplitude)
      (intrinsicShearMap amplitude) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [intrinsicShearConstant_coe amplitude hAmplitude]
  exact (intrinsicShearMap_dist_le amplitude hAmplitude first second).trans
    (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)

theorem intrinsicShear_inverse_lipschitz
    (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (hQuarter : amplitude <= 1 / 4) :
    LipschitzWith (intrinsicShearConstant amplitude)
      (intrinsicShearEquiv amplitude hAmplitude hQuarter).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  let firstSource :=
    (intrinsicShearEquiv amplitude hAmplitude hQuarter).symm first
  let secondSource :=
    (intrinsicShearEquiv amplitude hAmplitude hQuarter).symm second
  have hCo := intrinsicShearMap_colipschitz amplitude hAmplitude
    firstSource secondSource
  have hFirstApply : intrinsicShearMap amplitude firstSource = first :=
    (intrinsicShearEquiv amplitude hAmplitude hQuarter).apply_symm_apply first
  have hSecondApply : intrinsicShearMap amplitude secondSource = second :=
    (intrinsicShearEquiv amplitude hAmplitude hQuarter).apply_symm_apply second
  rw [hFirstApply, hSecondApply] at hCo
  have hFactor : 1 <= (1 + 4 * amplitude) * (1 - 2 * amplitude) := by
    nlinarith
  rw [intrinsicShearConstant_coe amplitude hAmplitude]
  calc
    dist firstSource secondSource <=
        ((1 + 4 * amplitude) * (1 - 2 * amplitude)) *
          dist firstSource secondSource :=
      le_mul_of_one_le_left dist_nonneg hFactor
    _ = (1 + 4 * amplitude) *
        ((1 - 2 * amplitude) * dist firstSource secondSource) := by ring
    _ <= (1 + 4 * amplitude) * dist first second :=
      mul_le_mul_of_nonneg_left hCo (by linarith)

def intrinsicShearHomeomorph
    (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (hQuarter : amplitude <= 1 / 4) : AmbientPlane ≃ₜ AmbientPlane where
  toEquiv := intrinsicShearEquiv amplitude hAmplitude hQuarter
  continuous_toFun := (intrinsicShear_forward_lipschitz amplitude hAmplitude).continuous
  continuous_invFun :=
    (intrinsicShear_inverse_lipschitz amplitude hAmplitude hQuarter).continuous

def intrinsicShearControlled
    (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (hQuarter : amplitude <= 1 / 4) : ControlledEquiv AmbientPlane AmbientPlane where
  toHomeomorph := intrinsicShearHomeomorph amplitude hAmplitude hQuarter
  forwardConstant := intrinsicShearConstant amplitude
  inverseConstant := intrinsicShearConstant amplitude
  forward_lipschitz := intrinsicShear_forward_lipschitz amplitude hAmplitude
  inverse_lipschitz := intrinsicShear_inverse_lipschitz amplitude hAmplitude hQuarter

def intrinsicShearCarrier : Set AmbientPlane :=
  Metric.closedBall 0 2

theorem intrinsicShearCarrier_compact : IsCompact intrinsicShearCarrier :=
  ProperSpace.isCompact_closedBall 0 2

theorem intrinsicShearMap_identity_outside
    (amplitude : Real) {point : AmbientPlane}
    (hPoint : point ∉ intrinsicShearCarrier) :
    intrinsicShearMap amplitude point = point := by
  have hNorm : 2 < ‖point‖ := by
    have hDistance : 2 < dist point 0 := by
      simpa [intrinsicShearCarrier, Metric.mem_closedBall] using hPoint
    simpa [dist_zero_right] using hDistance
  by_cases hZero : 1 <= |point 0|
  · have hBump : tentBump (point 0) = 0 :=
      tentBump_eq_zero_of_abs_ge_one hZero
    ext i
    fin_cases i <;> simp [intrinsicShearMap, shearKernel, planeEmbedding, hBump]
  · by_cases hOne : 1 <= |point 1|
    · have hBump : tentBump (point 1) = 0 :=
        tentBump_eq_zero_of_abs_ge_one hOne
      ext i
      fin_cases i <;> simp [intrinsicShearMap, shearKernel, planeEmbedding, hBump]
    · have hZeroAbs : |point 0| < 1 := lt_of_not_ge hZero
      have hOneAbs : |point 1| < 1 := lt_of_not_ge hOne
      have hZeroBounds := abs_lt.mp hZeroAbs
      have hOneBounds := abs_lt.mp hOneAbs
      have hSquared := ambient_norm_sq_eq_coordinates point
      have hNormNonnegative := norm_nonneg point
      exfalso
      nlinarith

theorem intrinsicShearControlled_identity_outside
    (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (hQuarter : amplitude <= 1 / 4) {point : AmbientPlane}
    (hPoint : point ∉ intrinsicShearCarrier) :
    intrinsicShearControlled amplitude hAmplitude hQuarter point = point :=
  intrinsicShearMap_identity_outside amplitude hPoint

theorem intrinsicShearControlled_inverse_identity_outside
    (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (hQuarter : amplitude <= 1 / 4) {point : AmbientPlane}
    (hPoint : point ∉ intrinsicShearCarrier) :
    (intrinsicShearControlled amplitude hAmplitude hQuarter).toHomeomorph.symm point =
      point := by
  apply (intrinsicShearControlled amplitude hAmplitude hQuarter).toHomeomorph.injective
  rw [(intrinsicShearControlled amplitude hAmplitude hQuarter).toHomeomorph.apply_symm_apply]
  exact (intrinsicShearControlled_identity_outside
    amplitude hAmplitude hQuarter hPoint).symm

def horizontalHalfProbe : AmbientPlane :=
  planeEmbedding { x := 1 / 2, y := 0 }

def verticalHalfProbe : AmbientPlane :=
  planeEmbedding { x := 0, y := 1 / 2 }

@[simp]
theorem horizontalHalfProbe_norm : ‖horizontalHalfProbe‖ = 1 / 2 := by
  have hSquared := ambient_norm_sq_eq_coordinates horizontalHalfProbe
  simp [horizontalHalfProbe, planeEmbedding] at hSquared
  change ‖!₂[(1 / 2 : Real), 0]‖ = 1 / 2
  nlinarith [norm_nonneg (!₂[(1 / 2 : Real), 0] : AmbientPlane)]

@[simp]
theorem verticalHalfProbe_norm : ‖verticalHalfProbe‖ = 1 / 2 := by
  have hSquared := ambient_norm_sq_eq_coordinates verticalHalfProbe
  simp [verticalHalfProbe, planeEmbedding] at hSquared
  change ‖!₂[(0 : Real), 1 / 2]‖ = 1 / 2
  nlinarith [norm_nonneg (!₂[(0 : Real), 1 / 2] : AmbientPlane)]

theorem halfProbes_equal_norm :
    ‖horizontalHalfProbe‖ = ‖verticalHalfProbe‖ := by
  rw [horizontalHalfProbe_norm, verticalHalfProbe_norm]

theorem horizontalHalfProbe_image_norm_sq :
    ‖intrinsicShearMap (1 / 4) horizontalHalfProbe‖ ^ 2 = 17 / 64 := by
  rw [ambient_norm_sq_eq_coordinates]
  norm_num [intrinsicShearMap, horizontalHalfProbe, shearKernel, tentBump,
    planeEmbedding]

theorem verticalHalfProbe_image_norm_sq :
    ‖intrinsicShearMap (1 / 4) verticalHalfProbe‖ ^ 2 = 25 / 64 := by
  rw [ambient_norm_sq_eq_coordinates]
  norm_num [intrinsicShearMap, verticalHalfProbe, shearKernel, tentBump,
    planeEmbedding]

theorem intrinsicShear_breaks_quarter_turn_symmetry :
    ‖horizontalHalfProbe‖ = ‖verticalHalfProbe‖ ∧
      ‖intrinsicShearMap (1 / 4) horizontalHalfProbe‖ ≠
        ‖intrinsicShearMap (1 / 4) verticalHalfProbe‖ := by
  refine ⟨halfProbes_equal_norm, ?_⟩
  intro hEqual
  have hSquares := congrArg (fun value : Real => value ^ 2) hEqual
  rw [horizontalHalfProbe_image_norm_sq,
    verticalHalfProbe_image_norm_sq] at hSquares
  norm_num at hSquares

def intrinsicAmplitude (n : Nat) : Real :=
  localAmplitude n / 2

theorem intrinsicAmplitude_nonnegative (n : Nat) :
    0 <= intrinsicAmplitude n := by
  exact div_nonneg (localAmplitude_nonnegative n) (by norm_num)

theorem intrinsicAmplitude_le_quarter (n : Nat) :
    intrinsicAmplitude n <= 1 / 4 := by
  dsimp [intrinsicAmplitude]
  linarith [localAmplitude_le_half n]

theorem intrinsicAmplitude_tendsto_quarter :
    Tendsto intrinsicAmplitude atTop (nhds (1 / 4 : Real)) := by
  change Tendsto (fun n => localAmplitude n / 2) atTop (nhds (1 / 4 : Real))
  convert localAmplitude_tendsto_half.div_const 2 using 1 <;> norm_num

def intrinsicShearFamily (n : Nat) : ControlledEquiv AmbientPlane AmbientPlane :=
  intrinsicShearControlled (intrinsicAmplitude n)
    (intrinsicAmplitude_nonnegative n) (intrinsicAmplitude_le_quarter n)

def limitIntrinsicShear : AmbientPlane ≃ₜ AmbientPlane :=
  intrinsicShearHomeomorph (1 / 4) (by norm_num) (by norm_num)

theorem intrinsicShearFamily_constant_bound (n : Nat) :
    ((intrinsicShearFamily n).forwardConstant : Real) <= 2 := by
  change (intrinsicShearConstant (intrinsicAmplitude n) : Real) <= 2
  rw [intrinsicShearConstant_coe _ (intrinsicAmplitude_nonnegative n)]
  linarith [intrinsicAmplitude_le_quarter n]

theorem intrinsicShearFamily_inverse_constant_bound (n : Nat) :
    ((intrinsicShearFamily n).inverseConstant : Real) <= 2 := by
  change (intrinsicShearConstant (intrinsicAmplitude n) : Real) <= 2
  rw [intrinsicShearConstant_coe _ (intrinsicAmplitude_nonnegative n)]
  linarith [intrinsicAmplitude_le_quarter n]

theorem intrinsicShearMap_amplitude_dist_le
    (firstAmplitude secondAmplitude : Real) (point : AmbientPlane) :
    dist (intrinsicShearMap firstAmplitude point)
        (intrinsicShearMap secondAmplitude point) <=
      dist firstAmplitude secondAmplitude := by
  rw [dist_eq_norm]
  have hDifference :
      intrinsicShearMap firstAmplitude point -
          intrinsicShearMap secondAmplitude point =
        planeEmbedding
          { x := 0
            y := (firstAmplitude - secondAmplitude) * shearKernel point } := by
    ext i
    fin_cases i <;>
      simp [intrinsicShearMap, planeEmbedding] <;> ring
  rw [hDifference, verticalVector_norm, abs_mul, Real.dist_eq]
  calc
    |firstAmplitude - secondAmplitude| * |shearKernel point| <=
        |firstAmplitude - secondAmplitude| * 1 := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [abs_of_nonneg (shearKernel_nonnegative point)]
      exact shearKernel_le_one point
    _ = |firstAmplitude - secondAmplitude| := by ring

theorem intrinsicShearFamily_tendsto_uniformly :
    TendstoUniformlyOn
      (fun n point => intrinsicShearFamily n point)
      limitIntrinsicShear atTop univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hEpsilon
  have hAmplitude := intrinsicAmplitude_tendsto_quarter
  rw [Metric.tendsto_atTop] at hAmplitude
  obtain ⟨N, hN⟩ := hAmplitude epsilon hEpsilon
  refine eventually_atTop.2 ⟨N, fun n hn point _ => ?_⟩
  change dist (intrinsicShearMap (1 / 4) point)
      (intrinsicShearMap (intrinsicAmplitude n) point) < epsilon
  exact (intrinsicShearMap_amplitude_dist_le _ _ _).trans_lt
    (by simpa [dist_comm] using hN n hn)

theorem intrinsicShearFamily_inverse_dist_le
    (n : Nat) (point : AmbientPlane) :
    dist (limitIntrinsicShear.symm point)
        ((intrinsicShearFamily n).toHomeomorph.symm point) <=
      2 * dist (intrinsicAmplitude n) (1 / 4 : Real) := by
  let limitSource := limitIntrinsicShear.symm point
  let currentSource := (intrinsicShearFamily n).toHomeomorph.symm point
  have hCo := intrinsicShearMap_colipschitz (1 / 4) (by norm_num)
    limitSource currentSource
  have hLimitApply : intrinsicShearMap (1 / 4) limitSource = point :=
    limitIntrinsicShear.apply_symm_apply point
  have hCurrentApply :
      intrinsicShearMap (intrinsicAmplitude n) currentSource = point :=
    (intrinsicShearFamily n).toHomeomorph.apply_symm_apply point
  have hAmplitudeDistance := intrinsicShearMap_amplitude_dist_le
    (1 / 4) (intrinsicAmplitude n) currentSource
  have hMapDistance :
      dist (intrinsicShearMap (1 / 4) limitSource)
          (intrinsicShearMap (1 / 4) currentSource) <=
        dist (intrinsicAmplitude n) (1 / 4 : Real) := by
    rw [hLimitApply]
    calc
      dist point (intrinsicShearMap (1 / 4) currentSource) =
          dist (intrinsicShearMap (1 / 4) currentSource) point := dist_comm _ _
      _ = dist (intrinsicShearMap (1 / 4) currentSource)
          (intrinsicShearMap (intrinsicAmplitude n) currentSource) := by
        rw [hCurrentApply]
      _ <= dist (1 / 4 : Real) (intrinsicAmplitude n) := hAmplitudeDistance
      _ = dist (intrinsicAmplitude n) (1 / 4 : Real) := dist_comm _ _
  have hHalf : (1 / 2 : Real) * dist limitSource currentSource <=
      dist (intrinsicAmplitude n) (1 / 4 : Real) := by
    calc
      (1 / 2 : Real) * dist limitSource currentSource =
          (1 - 2 * (1 / 4 : Real)) * dist limitSource currentSource := by ring
      _ <= dist (intrinsicShearMap (1 / 4) limitSource)
          (intrinsicShearMap (1 / 4) currentSource) := hCo
      _ <= dist (intrinsicAmplitude n) (1 / 4 : Real) := hMapDistance
  change dist limitSource currentSource <=
    2 * dist (intrinsicAmplitude n) (1 / 4 : Real)
  nlinarith

theorem inverse_intrinsicShearFamily_tendsto_uniformly :
    TendstoUniformlyOn
      (fun n point => (intrinsicShearFamily n).toHomeomorph.symm point)
      limitIntrinsicShear.symm atTop univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hEpsilon
  have hAmplitude := intrinsicAmplitude_tendsto_quarter
  rw [Metric.tendsto_atTop] at hAmplitude
  obtain ⟨N, hN⟩ := hAmplitude (epsilon / 2) (half_pos hEpsilon)
  refine eventually_atTop.2 ⟨N, fun n hn point _ => ?_⟩
  calc
    dist (limitIntrinsicShear.symm point)
        ((intrinsicShearFamily n).toHomeomorph.symm point) <=
        2 * dist (intrinsicAmplitude n) (1 / 4 : Real) :=
      intrinsicShearFamily_inverse_dist_le n point
    _ < 2 * (epsilon / 2) :=
      mul_lt_mul_of_pos_left (hN n hn) (by norm_num)
    _ = epsilon := by ring

theorem intrinsicShearFamily_identity_outside
    (n : Nat) {point : AmbientPlane} (hPoint : point ∉ intrinsicShearCarrier) :
    intrinsicShearFamily n point = point :=
  intrinsicShearControlled_identity_outside
    (intrinsicAmplitude n) (intrinsicAmplitude_nonnegative n)
    (intrinsicAmplitude_le_quarter n) hPoint

theorem limitIntrinsicShear_identity_outside
    {point : AmbientPlane} (hPoint : point ∉ intrinsicShearCarrier) :
    limitIntrinsicShear point = point :=
  intrinsicShearControlled_identity_outside (1 / 4) (by norm_num) (by norm_num) hPoint

def intrinsicShearModel (n : Nat)
    (model : ComputableBoundaryModel AmbientPlane) :
    ComputableBoundaryModel AmbientPlane :=
  transportComputableBoundaryModel (intrinsicShearFamily n) model

@[simp]
theorem intrinsicShearModel_interface (n : Nat)
    (model : ComputableBoundaryModel AmbientPlane) :
    (intrinsicShearModel n model).interface =
      intrinsicShearFamily n '' model.interface := rfl

theorem limitIntrinsicShear_interface_is_actual_frontier
    (model : ComputableBoundaryModel AmbientPlane) :
    frontier (limitIntrinsicShear '' model.inside) =
      limitIntrinsicShear '' model.interface :=
  limit_interface_is_actual_frontier limitIntrinsicShear model

theorem intrinsicShear_interfaces_converge
    (model : ComputableBoundaryModel AmbientPlane) :
    Tendsto
      (fun n => Metric.hausdorffDist
        (intrinsicShearModel n model).interface
        (limitIntrinsicShear '' model.interface))
      atTop (nhds 0) := by
  simpa only [intrinsicShearModel_interface] using
    uniform_images_converge_in_hausdorff
      (fun n point => intrinsicShearFamily n point)
      limitIntrinsicShear model.interface
      (intrinsicShearFamily_tendsto_uniformly.mono (subset_univ _))

theorem intrinsicShear_local_model_error_tendsto_zero
    (model : ComputableBoundaryModel AmbientPlane) :
    Tendsto
      (fun n => Metric.hausdorffDist
        ((intrinsicShearModel n model).approximation.carrier n)
        (intrinsicShearModel n model).interface)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact Metric.hausdorffDist_nonneg
  · intro n
    calc
      Metric.hausdorffDist
          ((intrinsicShearModel n model).approximation.carrier n)
          (intrinsicShearModel n model).interface <=
          (intrinsicShearFamily n).forwardConstant *
            model.approximation.envelope n :=
        transported_model_error_le (intrinsicShearFamily n) model n
      _ <= 2 * model.approximation.envelope n :=
        mul_le_mul_of_nonneg_right (intrinsicShearFamily_constant_bound n)
          (model_envelope_nonnegative model n)
  · simpa using
      tendsto_const_nhds.mul model.approximation.envelope_tendsto_zero

theorem intrinsicShear_computed_carriers_converge
    (model : ComputableBoundaryModel AmbientPlane) :
    Tendsto
      (fun n => Metric.hausdorffDist
        ((intrinsicShearModel n model).approximation.carrier n)
        (limitIntrinsicShear '' model.interface))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact Metric.hausdorffDist_nonneg
  · intro n
    let current := intrinsicShearModel n model
    have hFinite : Metric.hausdorffEDist
        (current.approximation.carrier n) current.interface ≠ ⊤ :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (current.approximation.carrier_nonempty n)
        current.approximation.target_nonempty
        (current.approximation.carrier_compact n).isBounded
        current.approximation.target_compact.isBounded
    exact Metric.hausdorffDist_triangle hFinite
  · simpa using
      (intrinsicShear_local_model_error_tendsto_zero model).add
        (intrinsicShear_interfaces_converge model)

theorem intrinsicShear_actual_frontier_limit
    (model : ComputableBoundaryModel AmbientPlane) :
    frontier (limitIntrinsicShear '' model.inside) =
        limitIntrinsicShear '' model.interface ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          (intrinsicShearModel n model).interface
          (limitIntrinsicShear '' model.interface))
        atTop (nhds 0) ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          ((intrinsicShearModel n model).approximation.carrier n)
          (limitIntrinsicShear '' model.interface))
        atTop (nhds 0) :=
  ⟨limitIntrinsicShear_interface_is_actual_frontier model,
    intrinsicShear_interfaces_converge model,
    intrinsicShear_computed_carriers_converge model⟩

end
end IntrinsicNonradialShearLimit
end BoundaryOfSelf
