import IntrinsicNonradialShearSlopeEnvelope

open scoped Topology RealInnerProductSpace
open Set Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearSlopeEnvelope

noncomputable def audit_radius_bound := @exactSlopeRadius_bound
noncomputable def audit_radius_witness := @slopeEnvelopeWitness_exact
noncomputable def audit_radius_sharp := @exactSlopeRadius_isSharp
noncomputable def audit_forward_regularity := @slopeEnvelope_forward_regularity_bound
noncomputable def audit_forward_strict := @slopeEnvelopeForwardRegularity_lt_coarse
noncomputable def audit_inverse_regularity := @slopeEnvelope_inverse_regularity_bound
noncomputable def audit_inverse_strict := @slopeEnvelopeInverseRegularity_lt_previous
noncomputable def audit_half_exact := half_slopeEnvelopeForwardRegularity_exact
noncomputable def audit_finite_inverse := @exists_slopeEnvelope_inverse_finiteCertificate

#print axioms audit_radius_bound
#print axioms audit_radius_witness
#print axioms audit_radius_sharp
#print axioms audit_forward_regularity
#print axioms audit_forward_strict
#print axioms audit_inverse_regularity
#print axioms audit_inverse_strict
#print axioms audit_half_exact
#print axioms audit_finite_inverse

end BoundaryOfSelf.IntrinsicNonradialShearSlopeEnvelope
