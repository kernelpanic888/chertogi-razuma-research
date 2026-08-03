import IntrinsicNonradialShearLimit

namespace BoundaryOfSelf
namespace IntrinsicNonradialShearLimitAudit

noncomputable section

open Filter
open Set
open StandardHausdorffMetricBridge
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport
open IntrinsicNonradialShearLimit

example (amplitude : Real) (hAmplitude : 0 <= amplitude)
    (hQuarter : amplitude <= 1 / 4) :
    ControlledEquiv AmbientPlane AmbientPlane :=
  intrinsicShearControlled amplitude hAmplitude hQuarter

example : IsCompact intrinsicShearCarrier :=
  intrinsicShearCarrier_compact

example :
    ‖horizontalHalfProbe‖ = ‖verticalHalfProbe‖ ∧
      ‖intrinsicShearMap (1 / 4) horizontalHalfProbe‖ ≠
        ‖intrinsicShearMap (1 / 4) verticalHalfProbe‖ :=
  intrinsicShear_breaks_quarter_turn_symmetry

example (n : Nat) :
    ((intrinsicShearFamily n).forwardConstant : Real) <= 2 :=
  intrinsicShearFamily_constant_bound n

example :
    TendstoUniformlyOn
      (fun n point => intrinsicShearFamily n point)
      limitIntrinsicShear atTop univ :=
  intrinsicShearFamily_tendsto_uniformly

example :
    TendstoUniformlyOn
      (fun n point => (intrinsicShearFamily n).toHomeomorph.symm point)
      limitIntrinsicShear.symm atTop univ :=
  inverse_intrinsicShearFamily_tendsto_uniformly

example (model : ComputableBoundaryModel AmbientPlane) :
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
  intrinsicShear_actual_frontier_limit model

#print axioms BoundaryOfSelf.IntrinsicNonradialShearLimit.intrinsicShear_inverse_lipschitz
#print axioms BoundaryOfSelf.IntrinsicNonradialShearLimit.intrinsicShearCarrier_compact
#print axioms BoundaryOfSelf.IntrinsicNonradialShearLimit.intrinsicShear_breaks_quarter_turn_symmetry
#print axioms BoundaryOfSelf.IntrinsicNonradialShearLimit.inverse_intrinsicShearFamily_tendsto_uniformly
#print axioms BoundaryOfSelf.IntrinsicNonradialShearLimit.intrinsicShear_actual_frontier_limit

end
end IntrinsicNonradialShearLimitAudit
end BoundaryOfSelf
