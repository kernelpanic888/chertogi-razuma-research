import ContourOrbitPotentialSeparation

namespace BoundaryOfSelf
namespace FiniteRadialBoundaryTheorem

open UniformRadialBoundaryFamily
open FiniteGridReachability
open FiniteAlternatingCycleKernel
open ConcreteRadialContourTraversal
open ThresholdCutBond
open MinimalSeparatingContourOrbit
open ContourOrbitPotentialSeparation

/-!
IF-BS-21 packages the complete finite radial-boundary theorem. The sampled
inside and outside are connected, the crossing set is a bond, every contour
state lies on a finite closed traversal, and the geometric edge set represented
by any selected orbit is the complete threshold cut. Hence the geometric
contour is independent of the selected anchor state.
-/

def EveryContourStateCloses {m : Nat} (hm : 0 < m) : Prop :=
  forall state : ContourState m,
    exists period : Nat, 0 < period /\
      iterate
        (successor (localInvolution (m := m)) (sharedInvolution hm))
        period state = state

theorem everyContourStateCloses {m : Nat} (hm : 0 < m) :
    EveryContourStateCloses hm := by
  intro state
  exact every_radial_contour_state_has_closed_cycle hm state

def SameGeometricOrbitCut {m : Nat} (hm : 0 < m)
    (left right : ContourState m) : Prop :=
  forall bridge : OrientedCrossing m,
    OrbitCut (SelectedOrbit hm left) bridge <->
      OrbitCut (SelectedOrbit hm right) bridge

theorem any_two_orbits_have_same_geometric_cut {m : Nat} (hm : 0 < m)
    (left right : ContourState m) :
    SameGeometricOrbitCut hm left right := by
  intro bridge
  constructor
  · intro _left_has
    exact contourOrbitCut_is_full hm right bridge
  · intro _right_has
    exact contourOrbitCut_is_full hm left bridge

structure FiniteRadialBoundaryCertificate (m : Nat) (hm : 0 < m) where
  inside_connected : forall left right : GridSample m,
    Inside left -> Inside right -> GridReachable Inside left right
  outside_connected : forall left right : GridSample m,
    (¬ Inside left) -> (¬ Inside right) ->
      GridReachable (fun point => ¬ Inside point) left right
  primal_threshold_bond : ThresholdCutIsBond m
  every_state_closes : EveryContourStateCloses hm
  every_orbit_separates : forall anchor : ContourState m,
    SeparatesSides (OrbitCut (SelectedOrbit hm anchor))
  every_orbit_is_full : forall anchor : ContourState m,
    forall bridge : OrientedCrossing m,
      OrbitCut (SelectedOrbit hm anchor) bridge
  geometric_cut_anchor_independent : forall left right : ContourState m,
    SameGeometricOrbitCut hm left right

def finiteRadialBoundaryCertificate {m : Nat} (hm : 0 < m) :
    FiniteRadialBoundaryCertificate m hm where
  inside_connected := any_two_inside_samples_connected
  outside_connected := any_two_outside_samples_connected hm
  primal_threshold_bond := radialThresholdCut_isBond hm
  every_state_closes := everyContourStateCloses hm
  every_orbit_separates := contourOrbitCut_separates hm
  every_orbit_is_full := contourOrbitCut_is_full hm
  geometric_cut_anchor_independent :=
    any_two_orbits_have_same_geometric_cut hm

theorem finite_radial_boundary_is_single_geometric_contour
    {m : Nat} (hm : 0 < m) :
    forall anchor : ContourState m,
      forall bridge : OrientedCrossing m,
        OrbitCut (SelectedOrbit hm anchor) bridge :=
  (finiteRadialBoundaryCertificate hm).every_orbit_is_full

end FiniteRadialBoundaryTheorem
end BoundaryOfSelf

#print axioms BoundaryOfSelf.FiniteRadialBoundaryTheorem.everyContourStateCloses
#print axioms BoundaryOfSelf.FiniteRadialBoundaryTheorem.any_two_orbits_have_same_geometric_cut
#print axioms BoundaryOfSelf.FiniteRadialBoundaryTheorem.finiteRadialBoundaryCertificate
#print axioms BoundaryOfSelf.FiniteRadialBoundaryTheorem.finite_radial_boundary_is_single_geometric_contour
