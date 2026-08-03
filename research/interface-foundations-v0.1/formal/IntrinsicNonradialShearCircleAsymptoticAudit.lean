import IntrinsicNonradialShearCircleAsymptotic

open scoped Topology RealInnerProductSpace
open Set Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearCircleAsymptotic

noncomputable def audit_witness_difference := @circleWitness_xSquare_difference
noncomputable def audit_witness_distance := @circleWitness_dist_sq
noncomputable def audit_ratio_exceeds := @circleWitness_ratio_exceeds
noncomputable def audit_coefficient_is_least := circle_xSquare_coefficient_one_isLeast
noncomputable def audit_first_lift_mem := @circleLiftFirst_mem
noncomputable def audit_second_lift_mem := @circleLiftSecond_mem
noncomputable def audit_lift_distance := @circleLift_dist_sq
noncomputable def audit_forward_cancellation := @circleLift_forward_cancellation
noncomputable def audit_forward_cancellation_abs := @circleLift_forward_cancellation_abs

#print axioms audit_witness_difference
#print axioms audit_witness_distance
#print axioms audit_ratio_exceeds
#print axioms audit_coefficient_is_least
#print axioms audit_first_lift_mem
#print axioms audit_second_lift_mem
#print axioms audit_lift_distance
#print axioms audit_forward_cancellation
#print axioms audit_forward_cancellation_abs

end BoundaryOfSelf.IntrinsicNonradialShearCircleAsymptotic
