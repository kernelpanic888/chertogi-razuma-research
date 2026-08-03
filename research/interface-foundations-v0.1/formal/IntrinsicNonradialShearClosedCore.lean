import IntrinsicNonradialShearCompactReduction

open Set Real

namespace BoundaryOfSelf.IntrinsicNonradialShearClosedCore

open LocalSegmentRealCompletion
open StandardHausdorffMetricBridge
open CompactTentHomeomorphism
open IntrinsicNonradialShearLimit
open IntrinsicNonradialShearExactSupport
open IntrinsicNonradialShearDeltaNet
open IntrinsicNonradialShearCompactReduction

theorem activeShortChordCore_closed (separation : ℝ) :
    _root_.IsClosed (ActiveShortChordCore separation) := by
  have hdistance :
      Continuous
        (fun pair : AmbientPlane × AmbientPlane => dist pair.1 pair.2) := by
    fun_prop
  have hshort :
      _root_.IsClosed
        {pair : AmbientPlane × AmbientPlane |
          dist pair.1 pair.2 ≤ separation} :=
    isClosed_le hdistance continuous_const
  have hcarrier : _root_.IsClosed intrinsicShearExactCarrier :=
    intrinsicShearExactCarrier_compact.isClosed
  change _root_.IsClosed
    ({pair : AmbientPlane × AmbientPlane |
        dist pair.1 pair.2 ≤ separation} ∩
      ({pair : AmbientPlane × AmbientPlane |
          pair.1 ∈ intrinsicShearExactCarrier} ∪
        {pair : AmbientPlane × AmbientPlane |
          pair.2 ∈ intrinsicShearExactCarrier}))
  exact hshort.inter
    ((hcarrier.preimage continuous_fst).union
      (hcarrier.preimage continuous_snd))

theorem activeOutputShortChordCore_closed
    {amplitude : ℝ} (ha : 0 ≤ amplitude) (separation : ℝ) :
    _root_.IsClosed (ActiveOutputShortChordCore amplitude separation) := by
  have hmap : Continuous (intrinsicShearMap amplitude) :=
    (intrinsicShear_forward_lipschitz amplitude ha).continuous
  have hdistance :
      Continuous
        (fun pair : AmbientPlane × AmbientPlane =>
          dist (intrinsicShearMap amplitude pair.1)
            (intrinsicShearMap amplitude pair.2)) :=
    (hmap.comp continuous_fst).dist (hmap.comp continuous_snd)
  have hshort :
      _root_.IsClosed
        {pair : AmbientPlane × AmbientPlane |
          dist (intrinsicShearMap amplitude pair.1)
            (intrinsicShearMap amplitude pair.2) ≤ separation} :=
    isClosed_le hdistance continuous_const
  have hcarrier : _root_.IsClosed intrinsicShearExactCarrier :=
    intrinsicShearExactCarrier_compact.isClosed
  change _root_.IsClosed
    ({pair : AmbientPlane × AmbientPlane |
        dist (intrinsicShearMap amplitude pair.1)
          (intrinsicShearMap amplitude pair.2) ≤ separation} ∩
      ({pair : AmbientPlane × AmbientPlane |
          pair.1 ∈ intrinsicShearExactCarrier} ∪
        {pair : AmbientPlane × AmbientPlane |
          pair.2 ∈ intrinsicShearExactCarrier}))
  exact hshort.inter
    ((hcarrier.preimage continuous_fst).union
      (hcarrier.preimage continuous_snd))

theorem activeShortChordCore_compact
    {separation : ℝ} (hseparation : 0 ≤ separation) :
    IsCompact (ActiveShortChordCore separation) :=
  (compactChordBox_compact (Real.sqrt 2 + separation)).of_isClosed_subset
    (activeShortChordCore_closed separation)
    (activeShortChordCore_subset_compactBox hseparation)

theorem activeOutputShortChordCore_compact
    {amplitude separation : ℝ}
    (ha : 0 ≤ amplitude) (hseparation : 0 ≤ separation) :
    IsCompact (ActiveOutputShortChordCore amplitude separation) :=
  (compactChordBox_compact
      (Real.sqrt 2 + separation + 2 * amplitude)).of_isClosed_subset
    (activeOutputShortChordCore_closed ha separation)
    (activeOutputShortChordCore_subset_compactBox ha hseparation)

def FiniteMetricDeltaNet
    {α : Type*} [PseudoMetricSpace α]
    (domain : Set α) (delta : ℝ) : Prop :=
  ∃ centers : Set α,
    centers.Finite ∧ centers ⊆ domain ∧
      ∀ point, point ∈ domain →
        ∃ center, center ∈ centers ∧ dist point center < delta

theorem finiteMetricDeltaNet_of_compact
    {α : Type*} [PseudoMetricSpace α]
    {domain : Set α} (hcompact : IsCompact domain)
    {delta : ℝ} (hdelta : 0 < delta) :
    FiniteMetricDeltaNet domain delta := by
  rcases Metric.finite_approx_of_totallyBounded
      hcompact.totallyBounded delta hdelta with
    ⟨centers, hcentersSubset, hcentersFinite, hcover⟩
  refine ⟨centers, hcentersFinite, hcentersSubset, ?_⟩
  intro point hpoint
  have hpointCover := hcover hpoint
  simp only [Set.mem_iUnion] at hpointCover
  rcases hpointCover with ⟨center, hcenter, hball⟩
  exact ⟨center, hcenter, by
    simpa [Metric.mem_ball, dist_comm] using hball⟩

def exactUpperReading
    {α : Type*} (value : α → ℝ) (point : α) : NoisyUpperReading α where
  point := point
  measured := value point
  error := 0

def SampleInside
    {α : Type*} (domain : Set α)
    (sample : List (NoisyUpperReading α)) : Prop :=
  ∀ reading, reading ∈ sample → reading.point ∈ domain

theorem compact_exists_finite_exactSample
    {α : Type*} [PseudoMetricSpace α]
    {domain : Set α} (hcompact : IsCompact domain)
    {delta : ℝ} (hdelta : 0 < delta) (value : α → ℝ) :
    ∃ sample : List (NoisyUpperReading α),
      NoisyUpperSampleValid value sample ∧
        DeltaCoverage domain sample delta ∧
          SampleInside domain sample := by
  classical
  rcases finiteMetricDeltaNet_of_compact hcompact hdelta with
    ⟨centers, hcentersFinite, hcentersSubset, hnet⟩
  let sample : List (NoisyUpperReading α) :=
    hcentersFinite.toFinset.toList.map (exactUpperReading value)
  refine ⟨sample, ?_, ?_, ?_⟩
  · intro reading hreading
    simp only [sample, List.mem_map] at hreading
    rcases hreading with ⟨point, _hpoint, rfl⟩
    simp [exactUpperReading]
  · intro point hpoint
    rcases hnet point hpoint with ⟨center, hcenter, hdistance⟩
    refine ⟨exactUpperReading value center, ?_, le_of_lt hdistance⟩
    simp [sample, exactUpperReading, hcenter]
  · intro reading hreading
    simp only [sample, List.mem_map] at hreading
    rcases hreading with ⟨point, hpoint, rfl⟩
    simpa [exactUpperReading] using
      hcentersSubset (by simpa using hpoint)

theorem compact_exists_finite_globalCertificate
    {α : Type*} [PseudoMetricSpace α]
    {domain : Set α} (hcompact : IsCompact domain)
    {delta : ℝ} (hdelta : 0 < delta) (value : α → ℝ) :
    ∃ sample : List (NoisyUpperReading α),
      NoisyUpperSampleValid value sample ∧
        DeltaCoverage domain sample delta ∧
          SampleInside domain sample ∧
            ∀ {constant : ℝ}, 0 ≤ constant →
              RegularityCertificate domain sample constant value →
                ∀ point, point ∈ domain →
                  value point ≤
                    noisySampleUpper sample + constant * delta := by
  rcases compact_exists_finite_exactSample hcompact hdelta value with
    ⟨sample, hvalid, hcoverage, hinside⟩
  refine ⟨sample, hvalid, hcoverage, hinside, ?_⟩
  intro constant hconstant hregular point hpoint
  exact global_le_noisySampleUpper_add_regularity
    hconstant hvalid hcoverage hregular point hpoint

theorem forwardCore_exists_finite_exactSample
    {separation delta : ℝ}
    (hseparation : 0 ≤ separation) (hdelta : 0 < delta)
    (value : (AmbientPlane × AmbientPlane) → ℝ) :
    ∃ sample : List (NoisyUpperReading (AmbientPlane × AmbientPlane)),
      NoisyUpperSampleValid value sample ∧
        DeltaCoverage (ActiveShortChordCore separation) sample delta ∧
          SampleInside (ActiveShortChordCore separation) sample :=
  compact_exists_finite_exactSample
    (activeShortChordCore_compact hseparation) hdelta value

theorem backwardCore_exists_finite_exactSample
    {amplitude separation delta : ℝ}
    (ha : 0 ≤ amplitude) (hseparation : 0 ≤ separation)
    (hdelta : 0 < delta)
    (value : (AmbientPlane × AmbientPlane) → ℝ) :
    ∃ sample : List (NoisyUpperReading (AmbientPlane × AmbientPlane)),
      NoisyUpperSampleValid value sample ∧
        DeltaCoverage
          (ActiveOutputShortChordCore amplitude separation) sample delta ∧
        SampleInside
          (ActiveOutputShortChordCore amplitude separation) sample :=
  compact_exists_finite_exactSample
    (activeOutputShortChordCore_compact ha hseparation) hdelta value

end BoundaryOfSelf.IntrinsicNonradialShearClosedCore
