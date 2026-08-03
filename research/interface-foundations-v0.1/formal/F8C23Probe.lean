import IntrinsicNonradialShearStationaryEnvelope

open BoundaryOfSelf.IntrinsicNonradialShearTangentEnvelope
open BoundaryOfSelf.IntrinsicNonradialShearStationaryEnvelope
open BoundaryOfSelf.IntrinsicNonradialShearDiagonalBlowUp
open BoundaryOfSelf.IntrinsicNonradialShearRealizableBlowUp
open BoundaryOfSelf.IntrinsicNonradialShearRealizableCertificate

#check exactTangentEnvelope
#check exactLocalTangentModulus
#check exactTangentEnvelope_eq_criticalProfile
#check slopeEnvelopeProfile
#check slopeStationaryBalance
#check existsUnique_slopeStationaryRoot
#check slopeEnvelopeProfile_unique_max
#check halfAmplitude_exactLocalTangentModulus
#check BoundaryOfSelf.IntrinsicNonradialShearTangentEnvelope.exactTangentWitnessPoint_mem
#check BoundaryOfSelf.IntrinsicNonradialShearTangentEnvelope.exactTangentWitnessPoint_density

#print BoundaryOfSelf.IntrinsicNonradialShearTangentEnvelope.exactLocalTangentModulus
#print BoundaryOfSelf.IntrinsicNonradialShearTangentEnvelope.tangentDensity
#print BoundaryOfSelf.IntrinsicNonradialShearTangentEnvelope.tangentForwardRaw
#print BoundaryOfSelf.IntrinsicNonradialShearTangentEnvelope.exactLocalTangentModulus_isGreatest

#check forwardBlowUpSq
#check directionalDiamondBand
#check diamond_unit_and_slope
#check diamond_width_le_sqrt_two
#check blowUp_x_sub_abs_le_dist
#check blowUp_y_sub_abs_le_dist
#check blowUp_slope_sub_abs_le_dist
#check direction_x_abs_le_one
#check direction_y_abs_le_one

#print BoundaryOfSelf.IntrinsicNonradialShearDiagonalBlowUp.forwardBlowUpSq
#print BoundaryOfSelf.IntrinsicNonradialShearRealizableBlowUp.directionalDiamondBand
#print BoundaryOfSelf.IntrinsicNonradialShearDiagonalBlowUp.directionalBlowUpChamber

namespace BoundaryOfSelf.IntrinsicNonradialShearChordBridge

open IntrinsicNonradialShearDiagonalBlowUp
open IntrinsicNonradialShearRealizableBlowUp
open IntrinsicNonradialShearRealizableCertificate
open IntrinsicNonradialShearTangentEnvelope
open IntrinsicNonradialShearStationaryEnvelope

/-- Explicit correction that turns the local tangent scale into a certified
finite-chord scale on the exact realizable diamond. -/
noncomputable def chordBridgeModulus (amplitude : ℝ) : ℝ :=
  2 * amplitude * (Real.sqrt 2 + 1) +
    2 * amplitude ^ 2 * Real.sqrt 2

lemma diamond_slope_abs_le_sqrt_two
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalDiamondBand) :
    |point.2| ≤ Real.sqrt 2 :=
  (diamond_unit_and_slope hpoint).2.trans
    (diamond_width_le_sqrt_two hpoint)

lemma diamond_y_abs_le_one
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalDiamondBand) :
    |point.1.ofLp 1| ≤ 1 :=
  direction_y_abs_le_one hpoint.1.1

lemma forwardBlowUpSq_eq_unit_excess
    {amplitude : ℝ} {point : BlowUpPoint}
    (hpoint : point ∈ directionalDiamondBand) :
    forwardBlowUpSq amplitude point =
      1 + 2 * amplitude * point.2 * point.1.ofLp 1 +
        amplitude ^ 2 * point.2 ^ 2 := by
  rw [forwardBlowUpSq]
  nlinarith [(diamond_unit_and_slope hpoint).1]

lemma slope_y_product_difference_bound
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand) :
    |first.2 * first.1.ofLp 1 - second.2 * second.1.ofLp 1| ≤
      (Real.sqrt 2 + 1) * dist first second := by
  have hslope := diamond_slope_abs_le_sqrt_two hfirst
  have hy := diamond_y_abs_le_one hsecond
  have hdy := blowUp_y_sub_abs_le_dist first second
  have hds := blowUp_slope_sub_abs_le_dist first second
  calc
    |first.2 * first.1.ofLp 1 - second.2 * second.1.ofLp 1| =
        |first.2 * (first.1.ofLp 1 - second.1.ofLp 1) +
          second.1.ofLp 1 * (first.2 - second.2)| := by ring_nf
    _ ≤ |first.2 * (first.1.ofLp 1 - second.1.ofLp 1)| +
          |second.1.ofLp 1 * (first.2 - second.2)| := abs_add_le _ _
    _ = |first.2| * |first.1.ofLp 1 - second.1.ofLp 1| +
          |second.1.ofLp 1| * |first.2 - second.2| := by
            rw [abs_mul, abs_mul]
    _ ≤ Real.sqrt 2 * dist first second + 1 * dist first second := by
      exact add_le_add
        (mul_le_mul hslope hdy (abs_nonneg _) (Real.sqrt_nonneg _))
        (mul_le_mul hy hds (abs_nonneg _) (by norm_num))
    _ = (Real.sqrt 2 + 1) * dist first second := by ring

lemma slope_square_difference_bound
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand) :
    |first.2 ^ 2 - second.2 ^ 2| ≤
      2 * Real.sqrt 2 * dist first second := by
  have hfirstSlope := diamond_slope_abs_le_sqrt_two hfirst
  have hsecondSlope := diamond_slope_abs_le_sqrt_two hsecond
  have hds := blowUp_slope_sub_abs_le_dist first second
  have hsum : |first.2 + second.2| ≤ 2 * Real.sqrt 2 := by
    calc
      |first.2 + second.2| ≤ |first.2| + |second.2| := abs_add_le _ _
      _ ≤ Real.sqrt 2 + Real.sqrt 2 := add_le_add hfirstSlope hsecondSlope
      _ = 2 * Real.sqrt 2 := by ring
  calc
    |first.2 ^ 2 - second.2 ^ 2| =
        |(first.2 - second.2) * (first.2 + second.2)| := by ring_nf
    _ = |first.2 - second.2| * |first.2 + second.2| := by rw [abs_mul]
    _ ≤ dist first second * (2 * Real.sqrt 2) := by
      exact mul_le_mul hds hsum (abs_nonneg _) dist_nonneg
    _ = 2 * Real.sqrt 2 * dist first second := by ring

/-- Every finite pair in the exact realizable diamond is controlled by the
explicit chord bridge modulus.  This is a global pairwise statement, unlike
the tangent envelope itself. -/
theorem forwardBlowUpSq_chord_bridge
    {amplitude : ℝ}
    (ha0 : 0 ≤ amplitude)
    {first second : BlowUpPoint}
    (hfirst : first ∈ directionalDiamondBand)
    (hsecond : second ∈ directionalDiamondBand) :
    |forwardBlowUpSq amplitude first - forwardBlowUpSq amplitude second| ≤
      chordBridgeModulus amplitude * dist first second := by
  have hprod := slope_y_product_difference_bound hfirst hsecond
  have hsq := slope_square_difference_bound hfirst hsecond
  have htwoa : 0 ≤ 2 * amplitude := mul_nonneg (by norm_num) ha0
  have ha2 : 0 ≤ amplitude ^ 2 := sq_nonneg amplitude
  rw [forwardBlowUpSq_eq_unit_excess hfirst,
    forwardBlowUpSq_eq_unit_excess hsecond]
  calc
    |(1 + 2 * amplitude * first.2 * first.1.ofLp 1 + amplitude ^ 2 * first.2 ^ 2) -
        (1 + 2 * amplitude * second.2 * second.1.ofLp 1 + amplitude ^ 2 * second.2 ^ 2)| =
        |(2 * amplitude) *
            (first.2 * first.1.ofLp 1 - second.2 * second.1.ofLp 1) +
          amplitude ^ 2 * (first.2 ^ 2 - second.2 ^ 2)| := by ring_nf
    _ ≤ |(2 * amplitude) *
            (first.2 * first.1.ofLp 1 - second.2 * second.1.ofLp 1)| +
          |amplitude ^ 2 * (first.2 ^ 2 - second.2 ^ 2)| := abs_add_le _ _
    _ = (2 * amplitude) *
            |first.2 * first.1.ofLp 1 - second.2 * second.1.ofLp 1| +
          amplitude ^ 2 * |first.2 ^ 2 - second.2 ^ 2| := by
      simp [abs_mul, abs_of_nonneg ha0, abs_of_nonneg ha2]
    _ ≤ (2 * amplitude) * ((Real.sqrt 2 + 1) * dist first second) +
          amplitude ^ 2 * (2 * Real.sqrt 2 * dist first second) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hprod htwoa)
        (mul_le_mul_of_nonneg_left hsq ha2)
    _ = chordBridgeModulus amplitude * dist first second := by
      rw [chordBridgeModulus]
      ring

theorem halfAmplitude_chordBridgeModulus :
    chordBridgeModulus (1 / 2 : ℝ) =
      1 + (3 / 2 : ℝ) * Real.sqrt 2 := by
  rw [chordBridgeModulus]
  ring

lemma tangentDensity_le_chord_profile
    {amplitude : ℝ}
    (ha0 : 0 ≤ amplitude)
    {point : BlowUpPoint}
    (hpoint : point ∈ directionalDiamondBand) :
    tangentDensity amplitude point ≤
      Real.sqrt 2 + 1 + amplitude * Real.sqrt 2 := by
  have hx := direction_x_abs_le_one hpoint.1.1
  have hy := direction_y_abs_le_one hpoint.1.1
  have hs := diamond_slope_abs_le_sqrt_two hpoint
  rw [tangentDensity, abs_mul]
  calc
    |point.1.ofLp 0| * |point.2| +
        |point.1.ofLp 1 + amplitude * point.2| ≤
        |point.1.ofLp 0| * |point.2| +
          (|point.1.ofLp 1| + |amplitude * point.2|) := by
            exact add_le_add (le_refl _)
              (abs_add_le (point.1.ofLp 1) (amplitude * point.2))
    _ = |point.1.ofLp 0| * |point.2| +
          (|point.1.ofLp 1| + amplitude * |point.2|) := by
            rw [abs_mul, abs_of_nonneg ha0]
    _ ≤ 1 * Real.sqrt 2 + (1 + amplitude * Real.sqrt 2) := by
      exact add_le_add
        (mul_le_mul hx hs (abs_nonneg _) (by norm_num))
        (add_le_add hy (mul_le_mul_of_nonneg_left hs ha0))
    _ = Real.sqrt 2 + 1 + amplitude * Real.sqrt 2 := by ring

/-- The tangent envelope sits below the explicit finite-chord certificate.
The difference is a genuine certified uncertainty budget, not an equality
claim. -/
theorem exactLocalTangentModulus_le_chordBridgeModulus
    {amplitude : ℝ}
    (ha0 : 0 ≤ amplitude) :
    exactLocalTangentModulus amplitude ≤ chordBridgeModulus amplitude := by
  have hw := tangentDensity_le_chord_profile ha0
    (exactTangentWitnessPoint_mem amplitude)
  have hfactor : 0 ≤ 2 * amplitude := mul_nonneg (by norm_num) ha0
  rw [exactLocalTangentModulus,
    ← exactTangentWitnessPoint_density ha0]
  calc
    2 * amplitude * tangentDensity amplitude (exactTangentWitnessPoint amplitude) ≤
        2 * amplitude *
          (Real.sqrt 2 + 1 + amplitude * Real.sqrt 2) :=
      mul_le_mul_of_nonneg_left hw hfactor
    _ = chordBridgeModulus amplitude := by
      rw [chordBridgeModulus]
      ring

noncomputable def chordBridgeGap (amplitude : ℝ) : ℝ :=
  chordBridgeModulus amplitude - exactLocalTangentModulus amplitude

theorem chordBridgeGap_nonneg
    {amplitude : ℝ}
    (ha0 : 0 ≤ amplitude) :
    0 ≤ chordBridgeGap amplitude := by
  rw [chordBridgeGap]
  exact sub_nonneg.mpr (exactLocalTangentModulus_le_chordBridgeModulus ha0)

theorem halfAmplitude_chordBridge_certificate :
    exactLocalTangentModulus (1 / 2 : ℝ) = halfAmplitudeEnvelopeValue ∧
      chordBridgeModulus (1 / 2 : ℝ) =
        1 + (3 / 2 : ℝ) * Real.sqrt 2 ∧
      0 ≤ chordBridgeGap (1 / 2 : ℝ) := by
  refine ⟨halfAmplitude_exactLocalTangentModulus,
    halfAmplitude_chordBridgeModulus, ?_⟩
  exact chordBridgeGap_nonneg (by norm_num)

end BoundaryOfSelf.IntrinsicNonradialShearChordBridge
