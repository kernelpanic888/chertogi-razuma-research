import IntrinsicNonradialShearExecutableCoarseNet

open Set Filter Topology

namespace BoundaryOfSelf.IntrinsicNonradialShearRationalParameterRefinement

noncomputable section

/-! ## IF-BS-22F-F8C31A: executable rational parameter refinement -/

def rationalGridValue (level : Nat) (index : Fin (level + 2)) : Rat :=
  -1 + 2 * (index.val : Rat) / (level + 1 : Nat)

def realGridValue (level : Nat) (index : Fin (level + 2)) : ℝ :=
  -1 + 2 * (index.val : ℝ) / (level + 1 : ℝ)

def parameterMeshRadius (level : Nat) : ℝ :=
  2 / (level + 1 : ℝ)

structure RationalParameterNode (level : Nat) where
  hemisphere : Bool
  tIndex : Fin (level + 2)
  vIndex : Fin (level + 2)
  deriving Repr, DecidableEq, Fintype

def RationalParameterNode.t
    {level : Nat} (node : RationalParameterNode level) : ℝ :=
  realGridValue level node.tIndex

def RationalParameterNode.v
    {level : Nat} (node : RationalParameterNode level) : ℝ :=
  realGridValue level node.vIndex

def RationalParameterNode.serializedT
    {level : Nat} (node : RationalParameterNode level) : Rat :=
  rationalGridValue level node.tIndex

def RationalParameterNode.serializedV
    {level : Nat} (node : RationalParameterNode level) : Rat :=
  rationalGridValue level node.vIndex

def parameterDistance
    {level : Nat} (t v : ℝ) (node : RationalParameterNode level) : ℝ :=
  max |t - node.t| |v - node.v|

theorem rationalGridValue_cast
    (level : Nat) (index : Fin (level + 2)) :
    ((rationalGridValue level index : Rat) : ℝ) =
      realGridValue level index := by
  norm_num [rationalGridValue, realGridValue]

theorem realGridValue_mem_Icc
    (level : Nat) (index : Fin (level + 2)) :
    realGridValue level index ∈ Set.Icc (-1 : ℝ) 1 := by
  have hden : 0 < (level + 1 : ℝ) := by positivity
  have hk0 : 0 ≤ (index.val : ℝ) := by positivity
  have hk : (index.val : ℝ) ≤ level + 1 := by
    exact_mod_cast Nat.le_of_lt_succ index.isLt
  have hratio0 :
      0 ≤ 2 * (index.val : ℝ) / (level + 1 : ℝ) := by positivity
  have hratio2 :
      2 * (index.val : ℝ) / (level + 1 : ℝ) ≤ 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  unfold realGridValue
  constructor <;> linarith

theorem exists_grid_index_close
    (level : Nat) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ index : Fin (level + 2),
      |x - realGridValue level index| ≤ parameterMeshRadius level := by
  let denominator : ℝ := level + 1
  let scaled : ℝ := (x + 1) * denominator / 2
  have hden : 0 < denominator := by
    dsimp [denominator]
    positivity
  have hscaled0 : 0 ≤ scaled := by
    dsimp [scaled]
    apply div_nonneg
    · exact mul_nonneg (by linarith [hx.1]) (by positivity)
    · norm_num
  have hscaledUpper : scaled ≤ denominator := by
    dsimp [scaled]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [hx.2]
  let indexNat : Nat := ⌊scaled⌋₊
  have hindexCastLower : (indexNat : ℝ) ≤ scaled := by
    exact Nat.floor_le hscaled0
  have hindexCastUpper : scaled < (indexNat : ℝ) + 1 := by
    exact Nat.lt_floor_add_one scaled
  have hindexNatUpper : indexNat ≤ level + 1 := by
    have hindexCastBound :
        (indexNat : ℝ) ≤ (level + 1 : ℝ) := by
      exact le_trans hindexCastLower (by simpa [denominator] using hscaledUpper)
    exact_mod_cast hindexCastBound
  let index : Fin (level + 2) :=
    ⟨indexNat, Nat.lt_succ_of_le hindexNatUpper⟩
  refine ⟨index, ?_⟩
  have hxIdentity :
      x - realGridValue level index =
        2 * (scaled - (indexNat : ℝ)) / denominator := by
    dsimp [scaled, denominator, index, realGridValue]
    field_simp
    ring
  have hdiff0 : 0 ≤ scaled - (indexNat : ℝ) := by linarith
  have hdiff1 : scaled - (indexNat : ℝ) ≤ 1 := by linarith
  rw [hxIdentity, abs_of_nonneg (by positivity)]
  rw [parameterMeshRadius]
  apply (div_le_div_iff₀ hden (by positivity : (0 : ℝ) < level + 1)).2
  dsimp [denominator]
  nlinarith

theorem exists_parameterNode_close
    (level : Nat) (hemisphere : Bool)
    {t v : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hv : v ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ node : RationalParameterNode level,
      node.hemisphere = hemisphere ∧
      parameterDistance t v node ≤ parameterMeshRadius level := by
  rcases exists_grid_index_close level ht with ⟨tIndex, htClose⟩
  rcases exists_grid_index_close level hv with ⟨vIndex, hvClose⟩
  let node : RationalParameterNode level :=
    { hemisphere := hemisphere
      tIndex := tIndex
      vIndex := vIndex }
  refine ⟨node, rfl, ?_⟩
  exact max_le htClose hvClose

theorem parameterNode_coordinates_mem
    {level : Nat} (node : RationalParameterNode level) :
    node.t ∈ Set.Icc (-1 : ℝ) 1 ∧
      node.v ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨realGridValue_mem_Icc level node.tIndex,
    realGridValue_mem_Icc level node.vIndex⟩

theorem parameterMeshRadius_nonnegative (level : Nat) :
    0 ≤ parameterMeshRadius level := by
  unfold parameterMeshRadius
  positivity

theorem parameterMeshRadius_tendsto_zero :
    Tendsto parameterMeshRadius atTop (𝓝 0) := by
  change Tendsto (fun n : Nat => 2 / (n + 1 : ℝ)) atTop (𝓝 0)
  have hbase :
      Tendsto (fun n : Nat => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hscaled := hbase.const_mul 2
  simpa [div_eq_mul_inv] using hscaled

theorem parameterMeshRadius_eventually_lt
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ level in atTop, parameterMeshRadius level < epsilon := by
  exact (tendsto_order.1 parameterMeshRadius_tendsto_zero).2
    epsilon hepsilon

end

end BoundaryOfSelf.IntrinsicNonradialShearRationalParameterRefinement
