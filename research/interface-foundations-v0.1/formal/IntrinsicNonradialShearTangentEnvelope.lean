import IntrinsicNonradialShearCircleAsymptotic

open scoped Topology RealInnerProductSpace
open Set Filter

namespace BoundaryOfSelf.IntrinsicNonradialShearTangentEnvelope

noncomputable section

open StandardHausdorffMetricBridge
open LocalSegmentRealCompletion
open IntrinsicNonradialShearExactSupport
open IntrinsicNonradialShearSpectralMap
open IntrinsicNonradialShearKernelSharp
open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearRealizableClosure
open IntrinsicNonradialShearRealizableCertificate
open IntrinsicNonradialShearSharpEnvelope
open IntrinsicNonradialShearCircleAsymptotic

/-! ## IF-BS-22F-F8C21: exact tangent envelope -/

def tangentForwardRaw
    (amplitude : ℝ) (point : BlowUpPoint) (angleSpeed slopeSpeed : ℝ) : ℝ :=
  2 * point.1.ofLp 0 * (-point.1.ofLp 1 * angleSpeed) +
    2 * (point.1.ofLp 1 + amplitude * point.2) *
      (point.1.ofLp 0 * angleSpeed + amplitude * slopeSpeed)

def tangentForwardDifferential
    (amplitude : ℝ) (point : BlowUpPoint) (angleSpeed slopeSpeed : ℝ) : ℝ :=
  2 * amplitude *
    (point.1.ofLp 0 * point.2 * angleSpeed +
      (point.1.ofLp 1 + amplitude * point.2) * slopeSpeed)

theorem tangentForwardRaw_eq_differential
    (amplitude : ℝ) (point : BlowUpPoint) (angleSpeed slopeSpeed : ℝ) :
    tangentForwardRaw amplitude point angleSpeed slopeSpeed =
      tangentForwardDifferential amplitude point angleSpeed slopeSpeed := by
  unfold tangentForwardRaw tangentForwardDifferential
  ring

def tangentMaxNorm (angleSpeed slopeSpeed : ℝ) : ℝ :=
  max |angleSpeed| |slopeSpeed|

def tangentDensity (amplitude : ℝ) (point : BlowUpPoint) : ℝ :=
  |point.1.ofLp 0 * point.2| +
    |point.1.ofLp 1 + amplitude * point.2|

def localTangentModulus (amplitude : ℝ) (point : BlowUpPoint) : ℝ :=
  2 * amplitude * tangentDensity amplitude point

theorem tangentForwardDifferential_le_localModulus
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude)
    (point : BlowUpPoint) {angleSpeed slopeSpeed : ℝ}
    (hspeed : tangentMaxNorm angleSpeed slopeSpeed ≤ 1) :
    |tangentForwardDifferential amplitude point angleSpeed slopeSpeed| ≤
      localTangentModulus amplitude point := by
  let A : ℝ := point.1.ofLp 0 * point.2
  let B : ℝ := point.1.ofLp 1 + amplitude * point.2
  have hangle : |angleSpeed| ≤ 1 :=
    (le_max_left |angleSpeed| |slopeSpeed|).trans hspeed
  have hslope : |slopeSpeed| ≤ 1 :=
    (le_max_right |angleSpeed| |slopeSpeed|).trans hspeed
  have hinside : |A * angleSpeed + B * slopeSpeed| ≤ |A| + |B| := by
    calc
      |A * angleSpeed + B * slopeSpeed| ≤
          |A * angleSpeed| + |B * slopeSpeed| := abs_add_le _ _
      _ = |A| * |angleSpeed| + |B| * |slopeSpeed| := by
        simp only [abs_mul]
      _ ≤ |A| * 1 + |B| * 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hangle (abs_nonneg A))
          (mul_le_mul_of_nonneg_left hslope (abs_nonneg B))
      _ = |A| + |B| := by ring
  have hfactor : 0 ≤ 2 * amplitude := by positivity
  calc
    |tangentForwardDifferential amplitude point angleSpeed slopeSpeed| =
        (2 * amplitude) * |A * angleSpeed + B * slopeSpeed| := by
      simp [tangentForwardDifferential, A, B, abs_mul,
        abs_of_nonneg hfactor]
    _ ≤ (2 * amplitude) * (|A| + |B|) :=
      mul_le_mul_of_nonneg_left hinside hfactor
    _ = localTangentModulus amplitude point := by
      simp [localTangentModulus, tangentDensity, A, B]

def maximizingSign (value : ℝ) : ℝ :=
  if 0 ≤ value then 1 else -1

lemma maximizingSign_abs (value : ℝ) :
    |maximizingSign value| = 1 := by
  by_cases h : 0 ≤ value <;> simp [maximizingSign, h]

lemma mul_maximizingSign (value : ℝ) :
    value * maximizingSign value = |value| := by
  by_cases h : 0 ≤ value
  · simp [maximizingSign, h, abs_of_nonneg h]
  · have hneg : value < 0 := lt_of_not_ge h
    simp [maximizingSign, h, abs_of_neg hneg]

def TangentUnitValues (amplitude : ℝ) (point : BlowUpPoint) : Set ℝ :=
  {value | ∃ angleSpeed slopeSpeed,
    tangentMaxNorm angleSpeed slopeSpeed ≤ 1 ∧
      value =
        |tangentForwardDifferential amplitude point angleSpeed slopeSpeed|}

theorem localTangentModulus_isGreatest
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) (point : BlowUpPoint) :
    IsGreatest (TangentUnitValues amplitude point)
      (localTangentModulus amplitude point) := by
  let A : ℝ := point.1.ofLp 0 * point.2
  let B : ℝ := point.1.ofLp 1 + amplitude * point.2
  let angleSpeed : ℝ := maximizingSign A
  let slopeSpeed : ℝ := maximizingSign B
  have hnorm : tangentMaxNorm angleSpeed slopeSpeed = 1 := by
    simp [tangentMaxNorm, angleSpeed, slopeSpeed, maximizingSign_abs]
  have hfactor : 0 ≤ 2 * amplitude := by positivity
  have heval :
      |tangentForwardDifferential amplitude point angleSpeed slopeSpeed| =
        localTangentModulus amplitude point := by
    rw [tangentForwardDifferential]
    change |2 * amplitude * (A * angleSpeed + B * slopeSpeed)| = _
    rw [show A * angleSpeed = |A| by
      simp [angleSpeed, mul_maximizingSign]]
    rw [show B * slopeSpeed = |B| by
      simp [slopeSpeed, mul_maximizingSign]]
    rw [abs_of_nonneg (mul_nonneg hfactor (add_nonneg (abs_nonneg A) (abs_nonneg B)))]
    simp [localTangentModulus, tangentDensity, A, B]
  constructor
  · exact ⟨angleSpeed, slopeSpeed, hnorm.le, heval.symm⟩
  · rintro value ⟨angleSpeed', slopeSpeed', hspeed, rfl⟩
    exact tangentForwardDifferential_le_localModulus ha0 point hspeed

def FirstQuadrantUnit : Set (ℝ × ℝ) :=
  (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∩
    {coordinates | coordinates.1 ^ 2 + coordinates.2 ^ 2 = 1}

def scalarTangentDensity (amplitude : ℝ) (coordinates : ℝ × ℝ) : ℝ :=
  coordinates.1 * (coordinates.1 + coordinates.2) + coordinates.2 +
    amplitude * (coordinates.1 + coordinates.2)

lemma firstQuadrantUnit_compact : IsCompact FirstQuadrantUnit := by
  apply (isCompact_Icc.prod isCompact_Icc).inter_right
  exact isClosed_eq (by fun_prop) (by fun_prop)

lemma firstQuadrantUnit_nonempty : FirstQuadrantUnit.Nonempty := by
  exact ⟨(1, 0), by norm_num [FirstQuadrantUnit]⟩

lemma scalarTangentDensity_continuous (amplitude : ℝ) :
    Continuous (scalarTangentDensity amplitude) := by
  unfold scalarTangentDensity
  fun_prop

theorem exists_scalarTangentDensity_max (amplitude : ℝ) :
    ∃ coordinates ∈ FirstQuadrantUnit,
      IsMaxOn (scalarTangentDensity amplitude) FirstQuadrantUnit coordinates :=
  firstQuadrantUnit_compact.exists_isMaxOn firstQuadrantUnit_nonempty
    (scalarTangentDensity_continuous amplitude).continuousOn

noncomputable def tangentEnvelopePoint (amplitude : ℝ) : ℝ × ℝ :=
  Classical.choose (exists_scalarTangentDensity_max amplitude)

lemma tangentEnvelopePoint_mem (amplitude : ℝ) :
    tangentEnvelopePoint amplitude ∈ FirstQuadrantUnit :=
  (Classical.choose_spec (exists_scalarTangentDensity_max amplitude)).1

lemma tangentEnvelopePoint_isMax (amplitude : ℝ) :
    IsMaxOn (scalarTangentDensity amplitude) FirstQuadrantUnit
      (tangentEnvelopePoint amplitude) :=
  (Classical.choose_spec (exists_scalarTangentDensity_max amplitude)).2

noncomputable def exactTangentEnvelope (amplitude : ℝ) : ℝ :=
  scalarTangentDensity amplitude (tangentEnvelopePoint amplitude)

lemma scalarTangentDensity_le_exact
    (amplitude : ℝ) {coordinates : ℝ × ℝ}
    (hcoordinates : coordinates ∈ FirstQuadrantUnit) :
    scalarTangentDensity amplitude coordinates ≤ exactTangentEnvelope amplitude :=
  tangentEnvelopePoint_isMax amplitude hcoordinates

lemma diamond_abs_coordinates_mem_firstQuadrant
    {point : BlowUpPoint} (hpoint : point ∈ directionalDiamondBand) :
    (|point.1.ofLp 0|, |point.1.ofLp 1|) ∈ FirstQuadrantUnit := by
  have hunit := (diamond_unit_and_slope hpoint).1
  have habsunit :
      |point.1.ofLp 0| ^ 2 + |point.1.ofLp 1| ^ 2 = 1 := by
    simpa [sq_abs] using hunit
  have hx1 : |point.1.ofLp 0| ≤ 1 := by
    nlinarith [sq_nonneg |point.1.ofLp 1|]
  have hy1 : |point.1.ofLp 1| ≤ 1 := by
    nlinarith [sq_nonneg |point.1.ofLp 0|]
  exact ⟨⟨⟨abs_nonneg _, hx1⟩, ⟨abs_nonneg _, hy1⟩⟩, habsunit⟩

theorem tangentDensity_le_exactTangentEnvelope
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude)
    {point : BlowUpPoint} (hpoint : point ∈ directionalDiamondBand) :
    tangentDensity amplitude point ≤ exactTangentEnvelope amplitude := by
  let X : ℝ := |point.1.ofLp 0|
  let Y : ℝ := |point.1.ofLp 1|
  let S : ℝ := |point.2|
  have hslope : S ≤ X + Y := hpoint.2
  have hshift :
      |point.1.ofLp 1 + amplitude * point.2| ≤ Y + amplitude * S := by
    calc
      |point.1.ofLp 1 + amplitude * point.2| ≤
          |point.1.ofLp 1| + |amplitude * point.2| := abs_add_le _ _
      _ = Y + amplitude * S := by
        simp [Y, S, abs_mul, abs_of_nonneg ha0]
  have hfactor : 0 ≤ X + amplitude := add_nonneg (abs_nonneg _) ha0
  have hscaled : (X + amplitude) * S ≤ (X + amplitude) * (X + Y) :=
    mul_le_mul_of_nonneg_left hslope hfactor
  calc
    tangentDensity amplitude point = X * S +
        |point.1.ofLp 1 + amplitude * point.2| := by
      simp [tangentDensity, X, S, abs_mul]
    _ ≤ X * S + (Y + amplitude * S) := by linarith
    _ = Y + (X + amplitude) * S := by ring
    _ ≤ Y + (X + amplitude) * (X + Y) := by linarith
    _ = scalarTangentDensity amplitude (X, Y) := by
      simp [scalarTangentDensity]
      ring
    _ ≤ exactTangentEnvelope amplitude :=
      scalarTangentDensity_le_exact amplitude
        (diamond_abs_coordinates_mem_firstQuadrant hpoint)

def tangentBoundaryPoint (coordinates : ℝ × ℝ) : BlowUpPoint :=
  (planeEmbedding
      ({x := coordinates.1, y := coordinates.2} : RealPlanePoint),
    coordinates.1 + coordinates.2)

lemma tangentBoundaryDirection_mem_sphere
    {coordinates : ℝ × ℝ}
    (hcoordinates : coordinates ∈ FirstQuadrantUnit) :
    (tangentBoundaryPoint coordinates).1 ∈ Metric.sphere kernelOrigin 1 := by
  rw [Metric.mem_sphere, dist_comm]
  have hunit : coordinates.1 ^ 2 + coordinates.2 ^ 2 = 1 := hcoordinates.2
  have hdistSq := dist_sq_eq_coordinate_sq_sum kernelOrigin
    (tangentBoundaryPoint coordinates).1
  have hx0 : kernelOrigin.ofLp 0 = 0 := by simp [kernelOrigin, planeEmbedding]
  have hy0 : kernelOrigin.ofLp 1 = 0 := by simp [kernelOrigin, planeEmbedding]
  have hx : (tangentBoundaryPoint coordinates).1.ofLp 0 = coordinates.1 := by
    simp [tangentBoundaryPoint, planeEmbedding]
  have hy : (tangentBoundaryPoint coordinates).1.ofLp 1 = coordinates.2 := by
    simp [tangentBoundaryPoint, planeEmbedding]
  rw [hx0, hy0] at hdistSq
  rw [hx, hy] at hdistSq
  simp only [zero_sub, neg_sq] at hdistSq
  have hsq :
      dist kernelOrigin (tangentBoundaryPoint coordinates).1 ^ 2 = 1 := by
    nlinarith
  have hnonneg :
      0 ≤ dist kernelOrigin (tangentBoundaryPoint coordinates).1 := dist_nonneg
  nlinarith

lemma tangentBoundaryPoint_mem
    {coordinates : ℝ × ℝ}
    (hcoordinates : coordinates ∈ FirstQuadrantUnit) :
    tangentBoundaryPoint coordinates ∈ directionalDiamondBand := by
  rcases hcoordinates.1 with ⟨⟨hX0, hX1⟩, ⟨hY0, hY1⟩⟩
  have hunit :
      (tangentBoundaryPoint coordinates).1.ofLp 0 ^ 2 +
        (tangentBoundaryPoint coordinates).1.ofLp 1 ^ 2 = 1 := by
    simpa [tangentBoundaryPoint, planeEmbedding] using hcoordinates.2
  have hwidth := unit_width_le_sqrt_two hunit
  have hsumle : coordinates.1 + coordinates.2 ≤ Real.sqrt 2 := by
    simpa [tangentBoundaryPoint, planeEmbedding, abs_of_nonneg hX0,
      abs_of_nonneg hY0] using hwidth
  rw [directionalDiamondBand]
  constructor
  · refine ⟨tangentBoundaryDirection_mem_sphere hcoordinates, ?_⟩
    constructor
    · change -Real.sqrt 2 ≤ coordinates.1 + coordinates.2
      nlinarith [Real.sqrt_nonneg 2]
    · exact hsumle
  · simp [tangentBoundaryPoint, planeEmbedding, abs_of_nonneg hX0,
      abs_of_nonneg hY0, abs_of_nonneg (add_nonneg hX0 hY0)]

lemma tangentDensity_boundary_exact
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude)
    {coordinates : ℝ × ℝ}
    (hcoordinates : coordinates ∈ FirstQuadrantUnit) :
    tangentDensity amplitude (tangentBoundaryPoint coordinates) =
      scalarTangentDensity amplitude coordinates := by
  rcases hcoordinates.1 with ⟨⟨hX0, hX1⟩, ⟨hY0, hY1⟩⟩
  have hsum0 : 0 ≤ coordinates.1 + coordinates.2 := add_nonneg hX0 hY0
  have hfirst0 : 0 ≤ coordinates.1 * (coordinates.1 + coordinates.2) :=
    mul_nonneg hX0 hsum0
  have hsecond0 :
      0 ≤ coordinates.2 + amplitude * (coordinates.1 + coordinates.2) :=
    add_nonneg hY0 (mul_nonneg ha0 hsum0)
  simp [tangentDensity, tangentBoundaryPoint, planeEmbedding,
    abs_of_nonneg hfirst0, abs_of_nonneg hsecond0, scalarTangentDensity]
  ring

noncomputable def exactTangentWitnessPoint (amplitude : ℝ) : BlowUpPoint :=
  tangentBoundaryPoint (tangentEnvelopePoint amplitude)

lemma exactTangentWitnessPoint_mem (amplitude : ℝ) :
    exactTangentWitnessPoint amplitude ∈ directionalDiamondBand :=
  tangentBoundaryPoint_mem (tangentEnvelopePoint_mem amplitude)

theorem exactTangentWitnessPoint_density
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    tangentDensity amplitude (exactTangentWitnessPoint amplitude) =
      exactTangentEnvelope amplitude := by
  exact tangentDensity_boundary_exact ha0 (tangentEnvelopePoint_mem amplitude)

theorem exactTangentEnvelope_isGreatest
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    IsGreatest
      (tangentDensity amplitude '' directionalDiamondBand)
      (exactTangentEnvelope amplitude) := by
  constructor
  · exact ⟨exactTangentWitnessPoint amplitude,
      exactTangentWitnessPoint_mem amplitude,
      exactTangentWitnessPoint_density ha0⟩
  · rintro value ⟨point, hpoint, rfl⟩
    exact tangentDensity_le_exactTangentEnvelope ha0 hpoint

noncomputable def exactLocalTangentModulus (amplitude : ℝ) : ℝ :=
  2 * amplitude * exactTangentEnvelope amplitude

def TangentChamberValues (amplitude : ℝ) : Set ℝ :=
  {value | ∃ point ∈ directionalDiamondBand,
    value ∈ TangentUnitValues amplitude point}

theorem exactLocalTangentModulus_isGreatest
    {amplitude : ℝ} (ha0 : 0 ≤ amplitude) :
    IsGreatest (TangentChamberValues amplitude)
      (exactLocalTangentModulus amplitude) := by
  have hfactor : 0 ≤ 2 * amplitude := by positivity
  have hwitnessDensity := exactTangentWitnessPoint_density ha0
  have hwitnessGreatest := localTangentModulus_isGreatest ha0
    (exactTangentWitnessPoint amplitude)
  constructor
  · refine ⟨exactTangentWitnessPoint amplitude,
      exactTangentWitnessPoint_mem amplitude, ?_⟩
    have hlocal :
        localTangentModulus amplitude (exactTangentWitnessPoint amplitude) =
          exactLocalTangentModulus amplitude := by
      simp [localTangentModulus, exactLocalTangentModulus, hwitnessDensity]
    rw [← hlocal]
    exact hwitnessGreatest.1
  · rintro value ⟨point, hpoint, hvalue⟩
    calc
      value ≤ localTangentModulus amplitude point :=
        (localTangentModulus_isGreatest ha0 point).2 hvalue
      _ ≤ exactLocalTangentModulus amplitude := by
        unfold localTangentModulus exactLocalTangentModulus
        exact mul_le_mul_of_nonneg_left
          (tangentDensity_le_exactTangentEnvelope ha0 hpoint) hfactor

end

end BoundaryOfSelf.IntrinsicNonradialShearTangentEnvelope
