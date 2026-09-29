import ForestUnimodality.BipartiteFractionalRounding

/-! The actual marginal-weight bound of stage 900, section 2.1.
The edge constraint holds on any graph; bipartiteness is used only for
the independently proved threshold rounding. -/
namespace ForestUnimodality

open Finset
variable {V : Type*} [DecidableEq V]

theorem erase_sdiff_closedNeighborhoodIn_of_adj (G : SimpleGraph V) (S : Finset V)
    {u v : V} (huv : G.Adj u v) :
    (S.erase v) \ closedNeighborhoodIn G (S.erase v) u =
      S \ closedNeighborhoodIn G S u := by
  ext x
  simp only [mem_sdiff_closedNeighborhoodIn, mem_erase]
  constructor
  · rintro ⟨⟨_, hx⟩, hxu, hno⟩
    exact ⟨hx, hxu, hno⟩
  · rintro ⟨hx, hxu, hno⟩
    exact ⟨⟨fun hxv => hno (hxv ▸ huv), hx⟩, hxu, hno⟩

/-- Conditional deletion identity for two adjacent vertices, using the
actual partition-function marginals rather than an assumed conditional law. -/
theorem hardCoreVertexMarginal_adj_delete (G : SimpleGraph V) (S : Finset V)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) (huv : G.Adj u v)
    {z : ℝ} (hz : 0 ≤ z) :
    hardCoreVertexMarginal G S z u =
      (1 - hardCoreVertexMarginal G S z v) * hardCoreVertexMarginal G (S.erase v) z u := by
  have hu' : u ∈ S.erase v := mem_erase.mpr ⟨huv.ne, hu⟩
  rw [hardCoreVertexMarginal_eq_delete_ratio G S hu z,
    hardCoreVertexMarginal_eq_delete_ratio G S hv z,
    hardCoreVertexMarginal_eq_delete_ratio G (S.erase v) hu' z,
    erase_sdiff_closedNeighborhoodIn_of_adj G S huv]
  have hr := partitionFunction_delete_vertex G S hv z
  have hZ := (partitionFunction_pos G S hz).ne'
  have hD := (partitionFunction_pos G (S.erase v) hz).ne'
  field_simp
  rw [hr]
  ring

theorem hardCoreVertexMarginal_adj_bound (G : SimpleGraph V) (S : Finset V)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) (huv : G.Adj u v)
    {z b : ℝ} (hz : 0 < z) (hzb : z ≤ b) :
    hardCoreVertexMarginal G S z u + (b / (1 + b)) * hardCoreVertexMarginal G S z v ≤
      b / (1 + b) := by
  have hb : 0 < b := hz.trans_le hzb
  have hqb : z / (1 + z) ≤ b / (1 + b) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hdel := (hardCoreVertexMarginal_le_activity G (S.erase v)
    (mem_erase.mpr ⟨huv.ne, hu⟩) hz).trans hqb
  have hnon : 0 ≤ 1 - hardCoreVertexMarginal G S z v :=
    sub_nonneg.mpr (hardCoreVertexMarginal_le_one G S hz.le v)
  have hmul := mul_le_mul_of_nonneg_left hdel hnon
  rw [← hardCoreVertexMarginal_adj_delete G S hu hv huv hz.le] at hmul
  nlinarith

namespace MarginalSelectionBound

noncomputable def selectionFraction (q x : ℝ) : ℝ :=
  max ((1 + q) / (2 * q) * x)
    ((1 + q) / (2 * q ^ 2) * x + (q - 1) / (2 * q))

theorem selectionFraction_mem_Icc {q x : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hx : 0 ≤ x) (hxq : x ≤ q) : selectionFraction q x ∈ Set.Icc 0 1 := by
  have hq0 : q ≠ 0 := hq.ne'
  constructor
  · exact (mul_nonneg (by positivity) hx).trans (le_max_left _ _)
  · apply max_le
    · rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 2 * q)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hxq (by positivity : 0 ≤ 1 + q)]
    · have h : (1 + q) / (2 * q ^ 2) * x + (q - 1) / (2 * q) ≤ 1 ↔
          (1 + q) * x + (q - 1) * q ≤ 2 * q ^ 2 := by
        constructor <;> intro hh <;> field_simp at hh ⊢ <;> nlinarith
      apply h.mpr
      nlinarith [mul_le_mul_of_nonneg_left hxq (by positivity : 0 ≤ 1 + q)]

theorem selectionFraction_add_le_one {q x y : ℝ} (hq : 0 < q)
    (hxy : x + q * y ≤ q) (hyx : q * x + y ≤ q) :
    selectionFraction q x + selectionFraction q y ≤ 1 := by
  have hq0 : q ≠ 0 := hq.ne'
  have hs : (1 + q) * (x + y) ≤ 2 * q := by nlinarith
  have hcross : (1 + q) * (x + q * y) ≤ (1 + q) * q :=
    mul_le_mul_of_nonneg_left hxy (by positivity)
  have hcross' : (1 + q) * (q * x + y) ≤ (1 + q) * q :=
    mul_le_mul_of_nonneg_left hyx (by positivity)
  unfold selectionFraction
  rcases le_total ((1 + q) / (2 * q) * x)
    ((1 + q) / (2 * q ^ 2) * x + (q - 1) / (2 * q)) with hx | hx <;>
    rcases le_total ((1 + q) / (2 * q) * y)
      ((1 + q) / (2 * q ^ 2) * y + (q - 1) / (2 * q)) with hy | hy
  all_goals
    simp only [max_eq_left hx, max_eq_right hx, max_eq_left hy, max_eq_right hy]
    field_simp
    nlinarith

end MarginalSelectionBound

open MarginalSelectionBound

/-- The manuscript's J_b, with the actual marginal at every vertex. -/
noncomputable def hardCoreMarginalSelectionScore (G : SimpleGraph V) (S : Finset V)
    (z b : ℝ) : ℝ :=
  ∑ v ∈ S, hardCoreVertexMarginal G S z v *
    selectionFraction (b / (1 + b)) (hardCoreVertexMarginal G S z v)

theorem IsMaximumMarginalIndependentOn.selection_bound
    {G : SimpleGraph V} {S I : Finset V} {z b : ℝ}
    (hI : IsMaximumMarginalIndependentOn G S I z) (hG : G.IsBipartite)
    (hz : 0 < z) (hzb : z ≤ b) :
    hardCoreMarginalSelectionScore G S z b ≤ hardCoreOccupiedMass G S I z := by
  have hb : 0 < b := hz.trans_le hzb
  have hq : 0 < b / (1 + b) := div_pos hb (by positivity)
  have hq1 : b / (1 + b) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hqz : z / (1 + z) ≤ b / (1 + b) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  apply hI.fractional_bound hG
    (fun v => selectionFraction (b / (1 + b)) (hardCoreVertexMarginal G S z v))
  · intro v hv
    exact selectionFraction_mem_Icc hq hq1
      (hardCoreVertexMarginal_nonneg G S hz.le v)
      ((hardCoreVertexMarginal_le_activity G S hv hz).trans hqz)
  · intro u hu v hv huv
    apply selectionFraction_add_le_one hq
      (hardCoreVertexMarginal_adj_bound G S hu hv huv hz hzb)
    have h := hardCoreVertexMarginal_adj_bound G S hv hu huv.symm hz hzb
    linarith

theorem IsMaximumMarginalIndependentOn.forest_selection_bound
    {G : SimpleGraph V} {S I : Finset V} {z b : ℝ}
    (hI : IsMaximumMarginalIndependentOn G S I z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hzb : z ≤ b) :
    hardCoreMarginalSelectionScore G S z b ≤ hardCoreOccupiedMass G S I z :=
  hI.selection_bound hG.isBipartite hz hzb

/-- A concrete maximizing independent set exists and attains the claimed
selection score; the lower bound is not a hypothesis in this existence result. -/
theorem exists_independent_marginal_selection_bound
    (G : SimpleGraph V) (S : Finset V) (hG : G.IsBipartite)
    {z b : ℝ} (hz : 0 < z) (hzb : z ≤ b) :
    ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet (I : Set V) ∧
      hardCoreMarginalSelectionScore G S z b ≤ hardCoreOccupiedMass G S I z := by
  obtain ⟨I, hI⟩ := exists_maximumWeightedIndependentOn G S (hardCoreVertexMarginal G S z)
  exact ⟨I, hI.subset, hI.independent,
    IsMaximumMarginalIndependentOn.selection_bound hI hG hz hzb⟩

/-- Conversion of a separately certified joint source bound into the
occupation-mass budget. The source bound itself remains explicit. -/
theorem IsMaximumMarginalIndependentOn.variance_le_mass_of_joint_bound
    {G : SimpleGraph V} {S I : Finset V} {z b CJ Cmu : ℝ}
    (hI : IsMaximumMarginalIndependentOn G S I z) (hG : G.IsBipartite)
    (hz : 0 < z) (hzb : z ≤ b) (hCJ : 0 ≤ CJ) (hCmu : 0 ≤ Cmu)
    (hvar : hardCoreVariance G S z ≤
      CJ * hardCoreMarginalSelectionScore G S z b + Cmu * hardCoreMean G S z) :
    hardCoreVariance G S z ≤ (CJ + 2 * Cmu) * hardCoreOccupiedMass G S I z := by
  have hscore := mul_le_mul_of_nonneg_left (hI.selection_bound hG hz hzb) hCJ
  have hhalf := hI.half_mean hG
  have hmean : hardCoreMean G S z ≤ 2 * hardCoreOccupiedMass G S I z := by linarith
  have hmean' := mul_le_mul_of_nonneg_left hmean hCmu
  nlinarith

#print axioms hardCoreVertexMarginal_adj_delete
#print axioms hardCoreVertexMarginal_adj_bound
#print axioms selectionFraction_add_le_one
#print axioms IsMaximumMarginalIndependentOn.selection_bound
#print axioms IsMaximumMarginalIndependentOn.forest_selection_bound
#print axioms exists_independent_marginal_selection_bound
#print axioms IsMaximumMarginalIndependentOn.variance_le_mass_of_joint_bound

end ForestUnimodality
