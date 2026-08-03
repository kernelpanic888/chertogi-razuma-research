import ControlledRadialTwistLimit

namespace BoundaryOfSelf
namespace NonradialEllipticTwistLimit

noncomputable section

open Filter
open Set
open StandardHausdorffMetricBridge
open BoundarySeparationInvariant
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport
open ControlledEquivComposition
open FiniteControlledChain
open UniformCauchyLimitCarrier
open TwoSidedLimitHomeomorph
open AnisotropicEllipseChamber
open CompactRadialTwistHomeomorphism
open SummableCompactTentWitness
open ControlledRadialTwistLimit

def reverseAnisotropicControlled : ControlledEquiv AmbientPlane AmbientPlane where
  toHomeomorph := anisotropicControlledEquiv.toHomeomorph.symm
  forwardConstant := anisotropicControlledEquiv.inverseConstant
  inverseConstant := anisotropicControlledEquiv.forwardConstant
  forward_lipschitz := anisotropicControlledEquiv.inverse_lipschitz
  inverse_lipschitz := anisotropicControlledEquiv.forward_lipschitz

@[simp]
theorem reverseAnisotropicControlled_apply (point : AmbientPlane) :
    reverseAnisotropicControlled point = anisotropicLinearEquiv.symm point := rfl

@[simp]
theorem reverseAnisotropicControlled_symm_apply (point : AmbientPlane) :
    reverseAnisotropicControlled.toHomeomorph.symm point =
      anisotropicLinearEquiv point := rfl

def ellipticTwistControlled (amplitude : Real) :
    ControlledEquiv AmbientPlane AmbientPlane :=
  composeControlled
    (composeControlled reverseAnisotropicControlled
      (controlledRadialTwist amplitude))
    anisotropicControlledEquiv

@[simp]
theorem ellipticTwistControlled_apply
    (amplitude : Real) (point : AmbientPlane) :
    ellipticTwistControlled amplitude point =
      anisotropicLinearEquiv
        (radialTwistMap amplitude (anisotropicLinearEquiv.symm point)) := rfl

@[simp]
theorem ellipticTwistControlled_symm_apply
    (amplitude : Real) (point : AmbientPlane) :
    (ellipticTwistControlled amplitude).toHomeomorph.symm point =
      anisotropicLinearEquiv
        (radialTwistMap (-amplitude) (anisotropicLinearEquiv.symm point)) := rfl

theorem ellipticTwist_inverse_is_negative
    (amplitude : Real) (point : AmbientPlane) :
    (ellipticTwistControlled amplitude).toHomeomorph.symm point =
      ellipticTwistControlled (-amplitude) point := by
  simp

theorem ellipticTwist_forwardConstant_coe (amplitude : Real) :
    ((ellipticTwistControlled amplitude).forwardConstant : Real) =
      2 * (1 + 2 * |amplitude|) := by
  simp [ellipticTwistControlled, reverseAnisotropicControlled,
    anisotropicControlledEquiv, controlledRadialTwist,
    radialTwistConstant_coe]

theorem ellipticTwist_inverseConstant_coe (amplitude : Real) :
    ((ellipticTwistControlled amplitude).inverseConstant : Real) =
      2 * (1 + 2 * |amplitude|) := by
  simp [ellipticTwistControlled, reverseAnisotropicControlled,
    anisotropicControlledEquiv, controlledRadialTwist,
    radialTwistConstant_coe]

def ellipticTwistSupport : Set AmbientPlane :=
  anisotropicLinearEquiv '' radialTwistSupport

theorem ellipticTwistSupport_compact : IsCompact ellipticTwistSupport := by
  exact radialTwistSupport_compact.image
    anisotropicContinuousLinearEquiv.continuous

theorem inverse_mem_radialSupport_of_mem_ellipticSupport
    {point : AmbientPlane} (hPoint : point ∈ ellipticTwistSupport) :
    anisotropicLinearEquiv.symm point ∈ radialTwistSupport := by
  rcases hPoint with ⟨source, hSource, rfl⟩
  simpa using hSource

theorem inverse_not_mem_radialSupport_of_not_mem_ellipticSupport
    {point : AmbientPlane} (hPoint : point ∉ ellipticTwistSupport) :
    anisotropicLinearEquiv.symm point ∉ radialTwistSupport := by
  intro hSource
  apply hPoint
  refine ⟨anisotropicLinearEquiv.symm point, hSource, ?_⟩
  exact anisotropicLinearEquiv.apply_symm_apply point

theorem ellipticTwist_identity_outside
    (amplitude : Real) {point : AmbientPlane}
    (hPoint : point ∉ ellipticTwistSupport) :
    ellipticTwistControlled amplitude point = point := by
  have hPreimage :=
    inverse_not_mem_radialSupport_of_not_mem_ellipticSupport hPoint
  have hRadial := radialTwist_identity_outside amplitude hPreimage
  change radialTwistMap amplitude (anisotropicLinearEquiv.symm point) =
    anisotropicLinearEquiv.symm point at hRadial
  rw [ellipticTwistControlled_apply, hRadial]
  exact anisotropicLinearEquiv.apply_symm_apply point

theorem ellipticTwist_inverse_identity_outside
    (amplitude : Real) {point : AmbientPlane}
    (hPoint : point ∉ ellipticTwistSupport) :
    (ellipticTwistControlled amplitude).toHomeomorph.symm point = point := by
  rw [ellipticTwist_inverse_is_negative]
  exact ellipticTwist_identity_outside (-amplitude) hPoint

def radialUnitPole : AmbientPlane :=
  planeEmbedding { x := 1, y := 0 }

def horizontalEllipticPole : AmbientPlane :=
  planeEmbedding { x := 2, y := 0 }

def verticalEqualNormProbe : AmbientPlane :=
  planeEmbedding { x := 0, y := 2 }

@[simp]
theorem radialUnitPole_norm : ‖radialUnitPole‖ = 1 := by
  have hSquared := ambient_norm_sq_eq_coordinates radialUnitPole
  simp [radialUnitPole, planeEmbedding] at hSquared
  change ‖!₂[(1 : Real), 0]‖ = 1
  rcases hSquared with hPositive | hNegative
  · exact hPositive
  · nlinarith [norm_nonneg (!₂[(1 : Real), 0] : AmbientPlane)]

@[simp]
theorem horizontalEllipticPole_norm : ‖horizontalEllipticPole‖ = 2 := by
  have hSquared := ambient_norm_sq_eq_coordinates horizontalEllipticPole
  simp [horizontalEllipticPole, planeEmbedding] at hSquared
  change ‖!₂[(2 : Real), 0]‖ = 2
  exact hSquared

@[simp]
theorem verticalEqualNormProbe_norm : ‖verticalEqualNormProbe‖ = 2 := by
  have hSquared := ambient_norm_sq_eq_coordinates verticalEqualNormProbe
  simp [verticalEqualNormProbe, planeEmbedding] at hSquared
  change ‖!₂[(0 : Real), 2]‖ = 2
  exact hSquared

theorem horizontalEllipticPole_mem_support :
    horizontalEllipticPole ∈ ellipticTwistSupport := by
  refine ⟨radialUnitPole, ?_, ?_⟩
  · simp [radialTwistSupport, Metric.mem_closedBall, dist_zero_right]
  · ext i
    fin_cases i <;>
      simp [radialUnitPole, horizontalEllipticPole,
        anisotropicLinearEquiv, planeEmbedding]

theorem anisotropic_vertical_probe_fixed :
    anisotropicLinearEquiv verticalEqualNormProbe = verticalEqualNormProbe := by
  ext i
  fin_cases i <;>
    simp [verticalEqualNormProbe, anisotropicLinearEquiv, planeEmbedding]

theorem verticalEqualNormProbe_not_mem_support :
    verticalEqualNormProbe ∉ ellipticTwistSupport := by
  intro hPoint
  rcases hPoint with ⟨source, hSource, hMap⟩
  have hSourceEq : source = verticalEqualNormProbe := by
    apply anisotropicLinearEquiv.injective
    exact hMap.trans anisotropic_vertical_probe_fixed.symm
  subst source
  have hDistance : dist verticalEqualNormProbe 0 <= 1 := by
    simpa [radialTwistSupport, Metric.mem_closedBall] using hSource
  have hNorm : ‖verticalEqualNormProbe‖ <= 1 := by
    simpa [dist_zero_right] using hDistance
  linarith [verticalEqualNormProbe_norm]

theorem ellipticTwistSupport_is_not_radial :
    ∃ first second : AmbientPlane,
      ‖first‖ = ‖second‖ ∧
      first ∈ ellipticTwistSupport ∧
      second ∉ ellipticTwistSupport := by
  exact ⟨horizontalEllipticPole, verticalEqualNormProbe, by simp,
    horizontalEllipticPole_mem_support,
    verticalEqualNormProbe_not_mem_support⟩

def ellipticTwistFamily (n : Nat) : ControlledEquiv AmbientPlane AmbientPlane :=
  ellipticTwistControlled (localAmplitude n)

def limitEllipticTwist : AmbientPlane ≃ₜ AmbientPlane :=
  (ellipticTwistControlled (1 / 2)).toHomeomorph

theorem ellipticTwistFamily_forward_bound (n : Nat) :
    ((ellipticTwistFamily n).forwardConstant : Real) <= 4 := by
  rw [ellipticTwistFamily, ellipticTwist_forwardConstant_coe]
  rw [abs_of_nonneg (localAmplitude_nonnegative n)]
  nlinarith [localAmplitude_le_half n]

theorem ellipticTwistFamily_inverse_bound (n : Nat) :
    ((ellipticTwistFamily n).inverseConstant : Real) <= 4 := by
  rw [ellipticTwistFamily, ellipticTwist_inverseConstant_coe]
  rw [abs_of_nonneg (localAmplitude_nonnegative n)]
  nlinarith [localAmplitude_le_half n]

theorem ellipticTwist_amplitude_dist_le
    (firstAmplitude secondAmplitude : Real) (point : AmbientPlane) :
    dist (ellipticTwistControlled firstAmplitude point)
        (ellipticTwistControlled secondAmplitude point) <=
      4 * dist firstAmplitude secondAmplitude := by
  let source := anisotropicLinearEquiv.symm point
  calc
    dist (ellipticTwistControlled firstAmplitude point)
        (ellipticTwistControlled secondAmplitude point) <=
        2 * dist (radialTwistMap firstAmplitude source)
          (radialTwistMap secondAmplitude source) := by
      have hStretch := anisotropic_forward_lipschitz.dist_le_mul
        (radialTwistMap firstAmplitude source)
        (radialTwistMap secondAmplitude source)
      change dist
          (anisotropicLinearEquiv (radialTwistMap firstAmplitude source))
          (anisotropicLinearEquiv (radialTwistMap secondAmplitude source)) <=
        2 * dist (radialTwistMap firstAmplitude source)
          (radialTwistMap secondAmplitude source) at hStretch
      simpa [source] using hStretch
    _ <= 2 * (2 * dist firstAmplitude secondAmplitude) :=
      mul_le_mul_of_nonneg_left
        (radialTwistMap_amplitude_dist_le firstAmplitude secondAmplitude source)
        (by norm_num)
    _ = 4 * dist firstAmplitude secondAmplitude := by ring

theorem ellipticTwistFamily_tendsto_uniformly :
    TendstoUniformlyOn
      (fun n point => ellipticTwistFamily n point)
      limitEllipticTwist atTop univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hEpsilon
  have hAmplitude := localAmplitude_tendsto_half
  rw [Metric.tendsto_atTop] at hAmplitude
  obtain ⟨N, hN⟩ := hAmplitude (epsilon / 4)
    (div_pos hEpsilon (by norm_num))
  refine eventually_atTop.2 ⟨N, fun n hn point _ => ?_⟩
  change dist (ellipticTwistControlled (1 / 2) point)
      (ellipticTwistControlled (localAmplitude n) point) < epsilon
  calc
    dist (ellipticTwistControlled (1 / 2) point)
        (ellipticTwistControlled (localAmplitude n) point) <=
        4 * dist (1 / 2 : Real) (localAmplitude n) :=
      ellipticTwist_amplitude_dist_le _ _ _
    _ = 4 * dist (localAmplitude n) (1 / 2 : Real) := by rw [dist_comm]
    _ < 4 * (epsilon / 4) :=
      mul_lt_mul_of_pos_left (hN n hn) (by norm_num)
    _ = epsilon := by ring

theorem inverse_ellipticTwistFamily_tendsto_uniformly :
    TendstoUniformlyOn
      (fun n point => (ellipticTwistFamily n).toHomeomorph.symm point)
      limitEllipticTwist.symm atTop univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hEpsilon
  have hAmplitude := localAmplitude_tendsto_half
  rw [Metric.tendsto_atTop] at hAmplitude
  obtain ⟨N, hN⟩ := hAmplitude (epsilon / 4)
    (div_pos hEpsilon (by norm_num))
  refine eventually_atTop.2 ⟨N, fun n hn point _ => ?_⟩
  rw [ellipticTwistFamily, ellipticTwist_inverse_is_negative]
  change dist (ellipticTwistControlled (-(1 / 2 : Real)) point)
      (ellipticTwistControlled (-localAmplitude n) point) < epsilon
  calc
    dist (ellipticTwistControlled (-(1 / 2 : Real)) point)
        (ellipticTwistControlled (-localAmplitude n) point) <=
        4 * dist (-(1 / 2 : Real)) (-localAmplitude n) :=
      ellipticTwist_amplitude_dist_le _ _ _
    _ = 4 * dist (localAmplitude n) (1 / 2 : Real) := by
      rw [Real.dist_eq, Real.dist_eq]
      congr 1
      ring_nf
    _ < 4 * (epsilon / 4) :=
      mul_lt_mul_of_pos_left (hN n hn) (by norm_num)
    _ = epsilon := by ring

theorem ellipticTwistFamily_identity_outside
    (n : Nat) {point : AmbientPlane} (hPoint : point ∉ ellipticTwistSupport) :
    ellipticTwistFamily n point = point :=
  ellipticTwist_identity_outside (localAmplitude n) hPoint

theorem limitEllipticTwist_identity_outside
    {point : AmbientPlane} (hPoint : point ∉ ellipticTwistSupport) :
    limitEllipticTwist point = point :=
  ellipticTwist_identity_outside (1 / 2) hPoint

def ellipticTwistModel (n : Nat)
    (model : ComputableBoundaryModel AmbientPlane) :
    ComputableBoundaryModel AmbientPlane :=
  transportComputableBoundaryModel (ellipticTwistFamily n) model

@[simp]
theorem ellipticTwistModel_interface (n : Nat)
    (model : ComputableBoundaryModel AmbientPlane) :
    (ellipticTwistModel n model).interface =
      ellipticTwistFamily n '' model.interface := rfl

theorem limitEllipticTwist_interface_is_actual_frontier
    (model : ComputableBoundaryModel AmbientPlane) :
    frontier (limitEllipticTwist '' model.inside) =
      limitEllipticTwist '' model.interface :=
  limit_interface_is_actual_frontier limitEllipticTwist model

theorem ellipticTwist_interfaces_converge
    (model : ComputableBoundaryModel AmbientPlane) :
    Tendsto
      (fun n => Metric.hausdorffDist
        (ellipticTwistModel n model).interface
        (limitEllipticTwist '' model.interface))
      atTop (nhds 0) := by
  simpa only [ellipticTwistModel_interface] using
    uniform_images_converge_in_hausdorff
      (fun n point => ellipticTwistFamily n point)
      limitEllipticTwist model.interface
      (ellipticTwistFamily_tendsto_uniformly.mono (subset_univ _))

theorem ellipticTwist_local_model_error_tendsto_zero
    (model : ComputableBoundaryModel AmbientPlane) :
    Tendsto
      (fun n => Metric.hausdorffDist
        ((ellipticTwistModel n model).approximation.carrier n)
        (ellipticTwistModel n model).interface)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact Metric.hausdorffDist_nonneg
  · intro n
    calc
      Metric.hausdorffDist
          ((ellipticTwistModel n model).approximation.carrier n)
          (ellipticTwistModel n model).interface <=
          (ellipticTwistFamily n).forwardConstant *
            model.approximation.envelope n :=
        transported_model_error_le (ellipticTwistFamily n) model n
      _ <= 4 * model.approximation.envelope n :=
        mul_le_mul_of_nonneg_right (ellipticTwistFamily_forward_bound n)
          (model_envelope_nonnegative model n)
  · simpa using
      tendsto_const_nhds.mul model.approximation.envelope_tendsto_zero

theorem ellipticTwist_computed_carriers_converge
    (model : ComputableBoundaryModel AmbientPlane) :
    Tendsto
      (fun n => Metric.hausdorffDist
        ((ellipticTwistModel n model).approximation.carrier n)
        (limitEllipticTwist '' model.interface))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact Metric.hausdorffDist_nonneg
  · intro n
    let current := ellipticTwistModel n model
    have hFinite : Metric.hausdorffEDist
        (current.approximation.carrier n) current.interface ≠ ⊤ :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (current.approximation.carrier_nonempty n)
        current.approximation.target_nonempty
        (current.approximation.carrier_compact n).isBounded
        current.approximation.target_compact.isBounded
    exact Metric.hausdorffDist_triangle hFinite
  · simpa using
      (ellipticTwist_local_model_error_tendsto_zero model).add
        (ellipticTwist_interfaces_converge model)

theorem ellipticTwist_actual_frontier_limit
    (model : ComputableBoundaryModel AmbientPlane) :
    frontier (limitEllipticTwist '' model.inside) =
        limitEllipticTwist '' model.interface ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          (ellipticTwistModel n model).interface
          (limitEllipticTwist '' model.interface))
        atTop (nhds 0) ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          ((ellipticTwistModel n model).approximation.carrier n)
          (limitEllipticTwist '' model.interface))
        atTop (nhds 0) :=
  ⟨limitEllipticTwist_interface_is_actual_frontier model,
    ellipticTwist_interfaces_converge model,
    ellipticTwist_computed_carriers_converge model⟩

end
end NonradialEllipticTwistLimit
end BoundaryOfSelf
