import IntrinsicNonradialShearSharpEnvelope

open scoped Topology RealInnerProductSpace
open Set Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearSharpEnvelope

noncomputable def audit_exact_lower := @exactDiamond_lower_bound
noncomputable def audit_exact_upper := @exactDiamond_upper_bound
noncomputable def audit_lower_witness := @lowerDiamondWitness_exact
noncomputable def audit_upper_witness := @upperDiamondWitness_exact
noncomputable def audit_sharp_envelope := @exactDiamond_envelope_isSharp
noncomputable def audit_inverse_extrema := @exactDiamond_inverse_extrema
noncomputable def audit_inverse_regularity := @sharpDiamond_inverse_regularity_bound
noncomputable def audit_no_worse := @sharpDiamondInverseRegularity_le_certified
noncomputable def audit_half_strict := @half_amplitude_sharpRegularity_strict
noncomputable def audit_finite_inverse := @exists_sharp_inverse_diamond_finiteCertificate

#print axioms audit_exact_lower
#print axioms audit_exact_upper
#print axioms audit_lower_witness
#print axioms audit_upper_witness
#print axioms audit_sharp_envelope
#print axioms audit_inverse_extrema
#print axioms audit_inverse_regularity
#print axioms audit_no_worse
#print axioms audit_half_strict
#print axioms audit_finite_inverse

end BoundaryOfSelf.IntrinsicNonradialShearSharpEnvelope
