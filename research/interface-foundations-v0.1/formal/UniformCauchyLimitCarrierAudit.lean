import UniformCauchyLimitCarrier

namespace BoundaryOfSelf
namespace UniformCauchyLimitCarrierAudit

open Filter
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport
open FiniteControlledChain
open UniformCauchyLimitCarrier

universe u

variable {X : Type u} [PseudoMetricSpace X] [CompleteSpace X]

example
    (maps : Nat -> X -> X) (target : Set X)
    (hCauchy : UniformCauchySeqOn maps atTop target) :
    exists limitMap : X -> X, TendstoUniformlyOn maps limitMap atTop target :=
  exists_uniform_limit_on maps target hCauchy

example
    (maps : Nat -> X -> X) (limitMap : X -> X) (target : Set X)
    (hUniform : TendstoUniformlyOn maps limitMap atTop target) :
    Tendsto
      (fun n => Metric.hausdorffDist (maps n '' target) (limitMap '' target))
      atTop (nhds 0) :=
  uniform_images_converge_in_hausdorff maps limitMap target hUniform

example
    (sequence : Nat -> ControlledEquiv X X) (model : ComputableBoundaryModel X)
    (hCauchy : PrefixUniformCauchy sequence model)
    (bound : Real)
    (hBound : ∀ depth, (prefixForwardProduct sequence depth : Real) ≤ bound) :
    exists limitMap : X -> X, exists limitCarrier : Set X,
      TendstoUniformlyOn
        (fun depth point => prefixControlledEquiv sequence depth point)
        limitMap atTop model.interface ∧
      IsCompact limitCarrier ∧
      limitCarrier.Nonempty ∧
      Tendsto
        (fun depth => Metric.hausdorffDist
          ((prefixComputableBoundaryModel sequence depth model).approximation.carrier depth)
          limitCarrier)
        atTop (nhds 0) :=
  exists_common_compact_limit_for_computed_carriers
    sequence model hCauchy bound hBound

#print axioms BoundaryOfSelf.UniformCauchyLimitCarrier.exists_uniform_limit_on
#print axioms BoundaryOfSelf.UniformCauchyLimitCarrier.uniform_images_converge_in_hausdorff
#print axioms BoundaryOfSelf.UniformCauchyLimitCarrier.exists_common_compact_limit_carrier
#print axioms BoundaryOfSelf.UniformCauchyLimitCarrier.exists_common_compact_limit_for_computed_carriers

end UniformCauchyLimitCarrierAudit
end BoundaryOfSelf
