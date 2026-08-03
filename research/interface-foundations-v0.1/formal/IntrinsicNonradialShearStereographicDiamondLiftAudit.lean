import IntrinsicNonradialShearStereographicDiamondLift

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearStereographicDiamondLiftAudit

open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearStereographicDiamondLift

theorem audited_coordinate_unit
    (hemisphere : Bool) (t : ℝ) :
    (stereographicDirection hemisphere t).ofLp 0 ^ 2 +
      (stereographicDirection hemisphere t).ofLp 1 ^ 2 = 1 :=
  stereographicDirection_coordinate_unit hemisphere t

theorem audited_lift_mem
    (hemisphere : Bool) (t : ℝ)
    {v : ℝ} (hv : v ∈ Set.Icc (-1 : ℝ) 1) :
    stereographicDiamondLift hemisphere t v ∈
      directionalDiamondBand :=
  stereographicDiamondLift_mem hemisphere t hv

theorem audited_two_chart_surjectivity :
    ∀ point ∈ directionalDiamondBand,
      ∃ hemisphere : Bool, ∃ t v : ℝ,
        t ∈ Set.Icc (-1 : ℝ) 1 ∧
        v ∈ Set.Icc (-1 : ℝ) 1 ∧
        stereographicDiamondLift hemisphere t v = point :=
  two_stereographic_charts_surjective

#print axioms audited_coordinate_unit
#print axioms audited_lift_mem
#print axioms audited_two_chart_surjectivity

end BoundaryOfSelf.IntrinsicNonradialShearStereographicDiamondLiftAudit
