import ControlledRadialTwistLimit

namespace BoundaryOfSelf
namespace ControlledRadialTwistLimitAudit

noncomputable section

open Filter
open Set
open StandardHausdorffMetricBridge
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport
open FiniteControlledChain
open CompactRadialTwistHomeomorphism
open ControlledRadialTwistLimit

example (angle : Real) (first second : AmbientPlane) :
    dist (rotatePoint angle first) (rotatePoint angle second) =
      dist first second :=
  rotatePoint_dist angle first second

example (amplitude : Real) :
    LipschitzWith (radialTwistConstant amplitude) (radialTwistMap amplitude) :=
  radialTwistMap_lipschitz amplitude

example (amplitude : Real) : ControlledEquiv AmbientPlane AmbientPlane :=
  controlledRadialTwist amplitude

example (n : Nat) (point : AmbientPlane) :
    prefixControlledEquiv radialTwistSequence n point =
      radialTwistHomeomorph (SummableCompactTentWitness.localAmplitude n) point :=
  prefix_radialTwist_apply n point

example (n : Nat) :
    ((prefixControlledEquiv radialTwistSequence n).forwardConstant : Real) <=
      Real.exp 1 :=
  prefix_radialTwist_forward_bound n

example :
    TendstoUniformlyOn
      (fun n point => prefixControlledEquiv radialTwistSequence n point)
      limitRadialTwist atTop univ :=
  prefix_radialTwists_tendsto_uniformly

example (model : ComputableBoundaryModel AmbientPlane) :
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
        atTop (nhds 0) :=
  exists_compact_radialTwist_limit model

#print axioms BoundaryOfSelf.ControlledRadialTwistLimit.rotatePoint_dist
#print axioms BoundaryOfSelf.ControlledRadialTwistLimit.radialTwistMap_lipschitz
#print axioms BoundaryOfSelf.ControlledRadialTwistLimit.prefix_radialTwist_forward_bound
#print axioms BoundaryOfSelf.ControlledRadialTwistLimit.prefix_radialTwists_tendsto_uniformly
#print axioms BoundaryOfSelf.ControlledRadialTwistLimit.exists_compact_radialTwist_limit

end
end ControlledRadialTwistLimitAudit
end BoundaryOfSelf
