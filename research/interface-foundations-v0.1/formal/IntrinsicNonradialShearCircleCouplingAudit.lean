import IntrinsicNonradialShearCircleCoupling

open scoped Topology RealInnerProductSpace
open Set Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearCircleCoupling

noncomputable def audit_coupled_bounds := @circle_xSquare_coupled_bounds
noncomputable def audit_circle_bound := @circle_xSquare_bound
noncomputable def audit_circle_strict := @circle_xSquare_strict
noncomputable def audit_diamond_strict := @diamond_xSquare_strict
noncomputable def audit_forward_bound := @circleCoupled_forward_regularity_bound
noncomputable def audit_forward_strict := @circleCoupled_forward_regularity_strict
noncomputable def audit_forward_gain := @circleCoupledForwardRegularity_lt_slopeEnvelope
noncomputable def audit_inverse_bound := @circleCoupled_inverse_regularity_bound
noncomputable def audit_inverse_gain := @circleCoupledInverseRegularity_lt_slopeEnvelope
noncomputable def audit_half_exact := half_circleCoupledForwardRegularity_exact
noncomputable def audit_finite_inverse := @exists_circleCoupled_inverse_finiteCertificate

#print axioms audit_coupled_bounds
#print axioms audit_circle_bound
#print axioms audit_circle_strict
#print axioms audit_diamond_strict
#print axioms audit_forward_bound
#print axioms audit_forward_strict
#print axioms audit_forward_gain
#print axioms audit_inverse_bound
#print axioms audit_inverse_gain
#print axioms audit_half_exact
#print axioms audit_finite_inverse

end BoundaryOfSelf.IntrinsicNonradialShearCircleCoupling
