import SummableTranslationWitness

namespace BoundaryOfSelf
namespace SummableTranslationWitnessAudit

open Filter
open Set
open AbstractBoundaryApproximation
open FiniteControlledChain
open SummableTranslationWitness

example (n : Nat) (point : Real) :
    prefixControlledEquiv translationSequence n point =
      point + (1 - (1 / 2 : Real) ^ n) := by
  simpa only [targetShift] using prefix_translation_apply n point

example :
    TendstoUniformlyOn
      (fun n point => prefixControlledEquiv translationSequence n point)
      (fun point : Real => point + 1) atTop univ :=
  prefix_translations_tendsto_uniformly

example :
    TendstoUniformlyOn
      (fun n point =>
        (prefixControlledEquiv translationSequence n).toHomeomorph.symm point)
      (fun point : Real => point - 1) atTop univ :=
  inverse_prefix_translations_tendsto_uniformly

example (model : ComputableBoundaryModel Real) :
    ∃ limitHomeomorph : Real ≃ₜ Real,
      limitHomeomorph = Homeomorph.addRight 1 ∧
      frontier (limitHomeomorph '' model.inside) =
        limitHomeomorph '' model.interface ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          (prefixComputableBoundaryModel translationSequence n model).interface
          (limitHomeomorph '' model.interface))
        atTop (nhds 0) ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          ((prefixComputableBoundaryModel translationSequence n model).approximation.carrier n)
          (limitHomeomorph '' model.interface))
        atTop (nhds 0) :=
  exists_unit_translation_limit model

#print axioms BoundaryOfSelf.SummableTranslationWitness.prefix_translation_apply
#print axioms BoundaryOfSelf.SummableTranslationWitness.prefix_translations_tendsto_uniformly
#print axioms BoundaryOfSelf.SummableTranslationWitness.inverse_prefix_translations_tendsto_uniformly
#print axioms BoundaryOfSelf.SummableTranslationWitness.exists_unit_translation_limit

end SummableTranslationWitnessAudit
end BoundaryOfSelf
