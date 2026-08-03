import NonradialEllipticTwistLimit

namespace BoundaryOfSelf
namespace NonradialEllipticTwistLimitAudit

noncomputable section

open Filter
open Set
open StandardHausdorffMetricBridge
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport
open NonradialEllipticTwistLimit

example (amplitude : Real) : ControlledEquiv AmbientPlane AmbientPlane :=
  ellipticTwistControlled amplitude

example (amplitude : Real) :
    ((ellipticTwistControlled amplitude).forwardConstant : Real) =
      2 * (1 + 2 * |amplitude|) :=
  ellipticTwist_forwardConstant_coe amplitude

example : IsCompact ellipticTwistSupport :=
  ellipticTwistSupport_compact

example :
    ∃ first second : AmbientPlane,
      ‖first‖ = ‖second‖ ∧
      first ∈ ellipticTwistSupport ∧
      second ∉ ellipticTwistSupport :=
  ellipticTwistSupport_is_not_radial

example :
    TendstoUniformlyOn
      (fun n point => ellipticTwistFamily n point)
      limitEllipticTwist atTop univ :=
  ellipticTwistFamily_tendsto_uniformly

example (model : ComputableBoundaryModel AmbientPlane) :
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
  ellipticTwist_actual_frontier_limit model

#print axioms BoundaryOfSelf.NonradialEllipticTwistLimit.ellipticTwistSupport_compact
#print axioms BoundaryOfSelf.NonradialEllipticTwistLimit.ellipticTwistSupport_is_not_radial
#print axioms BoundaryOfSelf.NonradialEllipticTwistLimit.ellipticTwistFamily_tendsto_uniformly
#print axioms BoundaryOfSelf.NonradialEllipticTwistLimit.ellipticTwist_computed_carriers_converge
#print axioms BoundaryOfSelf.NonradialEllipticTwistLimit.ellipticTwist_actual_frontier_limit

end
end NonradialEllipticTwistLimitAudit
end BoundaryOfSelf
