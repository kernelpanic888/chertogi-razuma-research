import IntrinsicNonradialShearTangentEnvelope

open scoped Topology RealInnerProductSpace
open Set Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearTangentEnvelope

noncomputable def audit_raw_identity := @tangentForwardRaw_eq_differential
noncomputable def audit_local_upper := @tangentForwardDifferential_le_localModulus
noncomputable def audit_local_exact := @localTangentModulus_isGreatest
noncomputable def audit_compact_max := @exists_scalarTangentDensity_max
noncomputable def audit_density_upper := @tangentDensity_le_exactTangentEnvelope
noncomputable def audit_boundary_mem := @tangentBoundaryPoint_mem
noncomputable def audit_boundary_exact := @tangentDensity_boundary_exact
noncomputable def audit_envelope_exact := @exactTangentEnvelope_isGreatest
noncomputable def audit_chamber_exact := @exactLocalTangentModulus_isGreatest

#print axioms audit_raw_identity
#print axioms audit_local_upper
#print axioms audit_local_exact
#print axioms audit_compact_max
#print axioms audit_density_upper
#print axioms audit_boundary_mem
#print axioms audit_boundary_exact
#print axioms audit_envelope_exact
#print axioms audit_chamber_exact

end BoundaryOfSelf.IntrinsicNonradialShearTangentEnvelope
