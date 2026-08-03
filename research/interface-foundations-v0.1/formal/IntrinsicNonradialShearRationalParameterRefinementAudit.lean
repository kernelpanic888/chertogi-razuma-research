import IntrinsicNonradialShearRationalParameterRefinement

namespace BoundaryOfSelf.IntrinsicNonradialShearRationalParameterRefinementAudit

open Set Filter Topology
open IntrinsicNonradialShearRationalParameterRefinement

theorem audited_rational_cast
    (level : Nat) (index : Fin (level + 2)) :
    ((rationalGridValue level index : Rat) : ℝ) =
      realGridValue level index :=
  rationalGridValue_cast level index

theorem audited_scalar_coverage
    (level : Nat) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ index : Fin (level + 2),
      |x - realGridValue level index| ≤ parameterMeshRadius level :=
  exists_grid_index_close level hx

theorem audited_pair_coverage
    (level : Nat) (hemisphere : Bool)
    {t v : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hv : v ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ node : RationalParameterNode level,
      node.hemisphere = hemisphere ∧
      parameterDistance t v node ≤ parameterMeshRadius level :=
  exists_parameterNode_close level hemisphere ht hv

theorem audited_radius_limit :
    Tendsto parameterMeshRadius atTop (𝓝 0) :=
  parameterMeshRadius_tendsto_zero

#print axioms audited_rational_cast
#print axioms audited_scalar_coverage
#print axioms audited_pair_coverage
#print axioms audited_radius_limit

end BoundaryOfSelf.IntrinsicNonradialShearRationalParameterRefinementAudit
