import CompactPlanarSlabWitness

namespace BoundaryOfSelf
namespace CompactPlanarSlabWitnessAudit

open Filter
open Set
open AbstractBoundaryApproximation
open FiniteControlledChain
open CompactPlanarSlabWitness

example : IsCompact planarSupport :=
  planarSupport_compact

example (n : Nat) (point : PlanarSlab) :
    prefixControlledEquiv planarSequence n point =
      (prefixControlledEquiv SummableCompactTentWitness.localTentSequence n point.1,
        point.2) :=
  prefix_planar_apply n point

example (n : Nat) :
    ((prefixControlledEquiv planarSequence n).forwardConstant : Real) <= 3 / 2 :=
  prefix_planar_forward_bound n

example (n : Nat) :
    ((prefixControlledEquiv planarSequence n).inverseConstant : Real) <= 2 :=
  prefix_planar_inverse_bound n

example (n : Nat) {point : PlanarSlab} (hPoint : point ∉ planarSupport) :
    planarSequence n point = point :=
  planar_step_identity_outside n hPoint

example {point : PlanarSlab} (hPoint : point ∉ planarSupport) :
    limitPlanarHomeomorph point = point :=
  limit_planar_identity_outside hPoint

example :
    TendstoUniformlyOn
      (fun n point => prefixControlledEquiv planarSequence n point)
      limitPlanarHomeomorph atTop univ :=
  prefix_planar_tendsto_uniformly

example (model : ComputableBoundaryModel PlanarSlab) :
    ∃ limitHomeomorph : PlanarSlab ≃ₜ PlanarSlab,
      limitHomeomorph = limitPlanarHomeomorph ∧
      frontier (limitHomeomorph '' model.inside) =
        limitHomeomorph '' model.interface ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          (prefixComputableBoundaryModel planarSequence n model).interface
          (limitHomeomorph '' model.interface))
        atTop (nhds 0) ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          ((prefixComputableBoundaryModel planarSequence n model).approximation.carrier n)
          (limitHomeomorph '' model.interface))
        atTop (nhds 0) :=
  exists_compact_planar_limit model

#print axioms BoundaryOfSelf.CompactPlanarSlabWitness.planarSupport_compact
#print axioms BoundaryOfSelf.CompactPlanarSlabWitness.prefix_planar_apply
#print axioms BoundaryOfSelf.CompactPlanarSlabWitness.prefix_planar_forward_bound
#print axioms BoundaryOfSelf.CompactPlanarSlabWitness.prefix_planar_inverse_bound
#print axioms BoundaryOfSelf.CompactPlanarSlabWitness.planar_step_identity_outside
#print axioms BoundaryOfSelf.CompactPlanarSlabWitness.exists_compact_planar_limit

end CompactPlanarSlabWitnessAudit
end BoundaryOfSelf
