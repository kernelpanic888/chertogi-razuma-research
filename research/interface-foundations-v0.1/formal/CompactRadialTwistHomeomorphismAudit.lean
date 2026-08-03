import CompactRadialTwistHomeomorphism

namespace BoundaryOfSelf
namespace CompactRadialTwistHomeomorphismAudit

noncomputable section

open Set
open StandardHausdorffMetricBridge
open CompactRadialTwistHomeomorphism

example (angle : Real) (point : AmbientPlane) :
    ‖rotatePoint angle point‖ = ‖point‖ :=
  rotatePoint_norm angle point

example (firstAngle secondAngle : Real) (point : AmbientPlane) :
    rotatePoint firstAngle (rotatePoint secondAngle point) =
      rotatePoint (firstAngle + secondAngle) point :=
  rotatePoint_add firstAngle secondAngle point

example (amplitude : Real) (point : AmbientPlane) :
    radialTwistMap (-amplitude) (radialTwistMap amplitude point) = point :=
  radialTwistMap_neg_comp amplitude point

example (amplitude : Real) : AmbientPlane ≃ₜ AmbientPlane :=
  radialTwistHomeomorph amplitude

example : IsCompact radialTwistSupport :=
  radialTwistSupport_compact

example (amplitude : Real) {point : AmbientPlane}
    (hPoint : point ∉ radialTwistSupport) :
    radialTwistHomeomorph amplitude point = point :=
  radialTwist_identity_outside amplitude hPoint

example (amplitude : Real) {point : AmbientPlane}
    (hPoint : point ∉ radialTwistSupport) :
    (radialTwistHomeomorph amplitude).symm point = point :=
  radialTwist_inverse_identity_outside amplitude hPoint

#print axioms BoundaryOfSelf.CompactRadialTwistHomeomorphism.rotatePoint_norm
#print axioms BoundaryOfSelf.CompactRadialTwistHomeomorphism.rotatePoint_add
#print axioms BoundaryOfSelf.CompactRadialTwistHomeomorphism.radialTwistMap_neg_comp
#print axioms BoundaryOfSelf.CompactRadialTwistHomeomorphism.radialTwistMap_continuous
#print axioms BoundaryOfSelf.CompactRadialTwistHomeomorphism.radialTwistSupport_compact
#print axioms BoundaryOfSelf.CompactRadialTwistHomeomorphism.radialTwist_identity_outside

end
end CompactRadialTwistHomeomorphismAudit
end BoundaryOfSelf
