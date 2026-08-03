import TwoSidedLimitHomeomorph

namespace BoundaryOfSelf
namespace TwoSidedLimitHomeomorphAudit

open Filter
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport
open FiniteControlledChain
open TwoSidedLimitHomeomorph

universe u

variable {X : Type u} [MetricSpace X] [CompleteSpace X]

example
    (sequence : Nat -> ControlledEquiv X X)
    (hForwardCauchy : UniformCauchySeqOn
      (fun depth point => prefixControlledEquiv sequence depth point) atTop Set.univ)
    (hInverseCauchy : UniformCauchySeqOn
      (fun depth point =>
        (prefixControlledEquiv sequence depth).toHomeomorph.symm point)
      atTop Set.univ)
    (forwardBound inverseBound : Real)
    (hForwardBound : ∀ depth,
      ((prefixControlledEquiv sequence depth).forwardConstant : Real) ≤ forwardBound)
    (hInverseBound : ∀ depth,
      ((prefixControlledEquiv sequence depth).inverseConstant : Real) ≤ inverseBound) :
    ∃ limitHomeomorph : X ≃ₜ X,
      TendstoUniformlyOn
        (fun depth point => prefixControlledEquiv sequence depth point)
        limitHomeomorph atTop Set.univ ∧
      TendstoUniformlyOn
        (fun depth point =>
          (prefixControlledEquiv sequence depth).toHomeomorph.symm point)
        limitHomeomorph.symm atTop Set.univ :=
  exists_limit_homeomorph sequence hForwardCauchy hInverseCauchy
    forwardBound inverseBound hForwardBound hInverseBound

example
    (limitHomeomorph : X ≃ₜ X) (model : ComputableBoundaryModel X) :
    frontier (limitHomeomorph '' model.inside) =
      limitHomeomorph '' model.interface :=
  limit_interface_is_actual_frontier limitHomeomorph model

#print axioms BoundaryOfSelf.TwoSidedLimitHomeomorph.moving_composition_tendsto
#print axioms BoundaryOfSelf.TwoSidedLimitHomeomorph.exists_limit_homeomorph
#print axioms BoundaryOfSelf.TwoSidedLimitHomeomorph.limit_interface_is_actual_frontier
#print axioms BoundaryOfSelf.TwoSidedLimitHomeomorph.exists_limit_homeomorph_and_actual_frontier

end TwoSidedLimitHomeomorphAudit
end BoundaryOfSelf
