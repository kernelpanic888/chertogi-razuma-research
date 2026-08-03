import SummableCompactTentWitness

namespace BoundaryOfSelf
namespace SummableCompactTentWitnessAudit

open Filter
open Set
open AbstractBoundaryApproximation
open FiniteControlledChain
open CompactTentHomeomorphism
open SummableCompactTentWitness

example (n : Nat) : 0 <= localAmplitude n :=
  localAmplitude_nonnegative n

example (n : Nat) : localAmplitude n <= 1 / 2 :=
  localAmplitude_le_half n

example (n : Nat) (point : Real) :
    prefixControlledEquiv localTentSequence n point =
      tentMap (localAmplitude n) point := by
  rw [prefix_localTent_apply, localTentPrefix_apply]

example (n : Nat) :
    ((prefixControlledEquiv localTentSequence n).forwardConstant : Real) <= 3 / 2 :=
  prefix_localTent_forward_bound n

example (n : Nat) :
    ((prefixControlledEquiv localTentSequence n).inverseConstant : Real) <= 2 :=
  prefix_localTent_inverse_bound n

example :
    TendstoUniformlyOn
      (fun n point => prefixControlledEquiv localTentSequence n point)
      limitLocalTent atTop univ :=
  prefix_localTents_tendsto_uniformly

example :
    TendstoUniformlyOn
      (fun n point =>
        (prefixControlledEquiv localTentSequence n).toHomeomorph.symm point)
      limitLocalTent.symm atTop univ :=
  inverse_prefix_localTents_tendsto_uniformly

example (model : ComputableBoundaryModel Real) :
    ∃ limitHomeomorph : Real ≃ₜ Real,
      limitHomeomorph = limitLocalTent ∧
      frontier (limitHomeomorph '' model.inside) =
        limitHomeomorph '' model.interface ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          (prefixComputableBoundaryModel localTentSequence n model).interface
          (limitHomeomorph '' model.interface))
        atTop (nhds 0) ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          ((prefixComputableBoundaryModel localTentSequence n model).approximation.carrier n)
          (limitHomeomorph '' model.interface))
        atTop (nhds 0) :=
  exists_compact_tent_limit model

example : limitLocalTent 0 = 1 / 2 :=
  limit_tent_is_nontrivial

#print axioms BoundaryOfSelf.SummableCompactTentWitness.prefix_localTent_apply
#print axioms BoundaryOfSelf.SummableCompactTentWitness.prefix_localTent_forwardConstant
#print axioms BoundaryOfSelf.SummableCompactTentWitness.prefix_localTent_inverseConstant
#print axioms BoundaryOfSelf.SummableCompactTentWitness.prefix_localTents_tendsto_uniformly
#print axioms BoundaryOfSelf.SummableCompactTentWitness.inverse_prefix_localTents_tendsto_uniformly
#print axioms BoundaryOfSelf.SummableCompactTentWitness.exists_compact_tent_limit

end SummableCompactTentWitnessAudit
end BoundaryOfSelf
