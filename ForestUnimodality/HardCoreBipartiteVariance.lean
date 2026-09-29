import ForestUnimodality.HardCoreMixtureMoments
import ForestUnimodality.HardCoreActivityWindow
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! A bipartite graph has a color class carrying at least half of its actual
occupation mass. The independently proved mixture variance identity then
gives Var(K) ≥ E(K)/(2(1+z)), with no assumed marginal or half-mass identity. -/

namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

/-- Actual occupation probability of one vertex, under the finite hard-core law. -/
noncomputable def hardCoreVertexMarginal (G : SimpleGraph V) (S : Finset V)
    (z : ℝ) (v : V) : ℝ := by
  classical
  exact (∑ K ∈ (independentSubsets G S).filter (fun K => v ∈ K), z ^ K.card) /
    partitionFunction G S z

noncomputable def hardCoreOccupiedMass (G : SimpleGraph V) (S A : Finset V)
    (z : ℝ) : ℝ := ∑ v ∈ A, hardCoreVertexMarginal G S z v

theorem hardCoreVertexMarginal_nonneg (G : SimpleGraph V) (S : Finset V)
    {z : ℝ} (hz : 0 ≤ z) (v : V) : 0 ≤ hardCoreVertexMarginal G S z v := by
  classical
  exact div_nonneg (sum_nonneg fun K _ => pow_nonneg hz _) (partitionFunction_pos G S hz).le

theorem hardCoreVertexMarginal_le_one (G : SimpleGraph V) (S : Finset V)
    {z : ℝ} (hz : 0 ≤ z) (v : V) : hardCoreVertexMarginal G S z v ≤ 1 := by
  classical
  unfold hardCoreVertexMarginal
  apply (div_le_one (partitionFunction_pos G S hz)).mpr
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun K _ _ => pow_nonneg hz _)

theorem hardCoreMean_eq_sum_vertex_marginals (G : SimpleGraph V) (S : Finset V)
    (z : ℝ) : hardCoreMean G S z = hardCoreOccupiedMass G S S z := by
  classical
  rw [hardCoreMean, hardCore_first_moment_eq_sum_vertices, sum_div]
  apply sum_congr rfl
  intro v hv
  rw [hardCoreVertexMarginal, sum_independent_containing_vertex G S hv z]

theorem hardCoreOccupiedMass_eq_intersection_expectation (G : SimpleGraph V)
    (S A : Finset V) (z : ℝ) :
    hardCoreOccupiedMass G S A z =
      (∑ K ∈ independentSubsets G S, ((K ∩ A).card : ℝ) * z ^ K.card) /
        partitionFunction G S z := by
  classical
  simp only [hardCoreOccupiedMass, hardCoreVertexMarginal, ← sum_div, sum_filter]
  rw [sum_comm]
  congr 1
  apply sum_congr rfl
  intro K _
  rw [← sum_filter]
  have hfilter : A.filter (fun v => v ∈ K) = K ∩ A := by ext v; simp [and_comm]
  rw [hfilter]
  simp

/-- The same independent-set splitting bijection with an arbitrary statistic
of the outside and inside parts. -/
theorem sum_independent_split_statistic {R : Type*} [AddCommMonoid R]
    (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) (F : Finset V → Finset V → R) :
    (∑ K ∈ independentSubsets G S, F (K \ I) (K ∩ I)) =
      ∑ J ∈ independentSubsets G (S \ I), ∑ T ∈ (available G I J).powerset, F J T := by
  classical
  rw [sum_sigma']
  apply sum_bij' (fun K _ => (⟨K \ I, K ∩ I⟩ : (J : Finset V) × Finset V))
    (fun p _ => p.1 ∪ p.2)
  · intro K hK
    exact mem_sigma.mpr ⟨split_left_mem hK, mem_powerset.mpr (split_right_subset hK)⟩
  · intro p hp
    obtain ⟨hJ, hT⟩ := mem_sigma.mp hp
    exact join_mem hIS hI hJ (mem_powerset.mp hT)
  · intro K _
    exact split_union K I
  · intro p hp
    obtain ⟨hJ, hT⟩ := mem_sigma.mp hp
    exact Sigma.ext (join_sdiff hJ (mem_powerset.mp hT))
      (heq_of_eq (join_inter hJ (mem_powerset.mp hT)))
  · intro K _
    rfl

theorem hardCoreOccupiedMass_complement_eq_layer_first_index
    (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) (z : ℝ) :
    hardCoreOccupiedMass G S (S \ I) z =
      ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
        hardCoreLayerWeight G S I z j m * (j : ℝ) := by
  classical
  rw [hardCoreOccupiedMass_eq_intersection_expectation]
  have hcard : ∀ K ∈ independentSubsets G S, K ∩ (S \ I) = K \ I := by
    intro K hK
    have hKS := (mem_independentSubsets.mp hK).1
    ext v
    simp only [mem_inter, mem_sdiff]
    tauto
  have hsplit : (∑ K ∈ independentSubsets G S, ((K ∩ (S \ I)).card : ℝ) * z ^ K.card) =
      ∑ J ∈ independentSubsets G (S \ I),
        (J.card : ℝ) * z ^ J.card * (1 + z) ^ (available G I J).card := by
    calc
      _ = ∑ K ∈ independentSubsets G S,
          ((K \ I).card : ℝ) * z ^ ((K \ I).card + (K ∩ I).card) := by
        apply sum_congr rfl
        intro K hK
        rw [hcard K hK, ← split_card]
      _ = ∑ J ∈ independentSubsets G (S \ I),
          ∑ T ∈ (available G I J).powerset, (J.card : ℝ) * z ^ (J.card + T.card) :=
        sum_independent_split_statistic G S I hIS hI
          (fun J T => (J.card : ℝ) * z ^ (J.card + T.card))
      _ = _ := by
        apply sum_congr rfl
        intro J _
        rw [← mul_sum, sum_powerset_pow_add_card]
        ring
  rw [hsplit, sum_independentSubsets_by_layers G I (S \ I)
    (fun j m => (j : ℝ) * z ^ j * (1 + z) ^ m)]
  simp only [sum_div, hardCoreLayerWeight]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro m _
  ring

theorem hardCoreOccupiedMass_add_complement (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (z : ℝ) :
    hardCoreOccupiedMass G S I z + hardCoreOccupiedMass G S (S \ I) z =
      hardCoreMean G S z := by
  rw [hardCoreMean_eq_sum_vertex_marginals]
  unfold hardCoreOccupiedMass
  have hdis : Disjoint I (S \ I) := disjoint_left.mpr (by
    intro v hv hvs; exact (mem_sdiff.mp hvs).2 hv)
  rw [← sum_union hdis, union_sdiff_of_subset hIS]

/-- Occupation of the chosen independent subset is exactly q times the
expected availability in the actual graph mixture. -/
theorem hardCoreOccupiedMass_eq_activity_available_mean
    (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z : ℝ} (hz : 0 < z) :
    hardCoreOccupiedMass G S I z = (z / (1 + z)) * hardCoreAvailableMean G S I z := by
  have hmean := hardCoreMean_eq_layer_mean G S I hIS hI hz
  have hpoint (j m : ℕ) : hardCoreLayerWeight G S I z j m * binomialLayerMean j m z =
      hardCoreLayerWeight G S I z j m * (j : ℝ) +
      (z / (1 + z)) * (hardCoreLayerWeight G S I z j m * (m : ℝ)) := by
    dsimp [binomialLayerMean]
    ring
  simp_rw [hpoint] at hmean
  simp only [sum_add_distrib, ← mul_sum] at hmean
  rw [← hardCoreOccupiedMass_complement_eq_layer_first_index G S I hIS hI z] at hmean
  change hardCoreMean G S z = hardCoreOccupiedMass G S (S \ I) z +
    (z / (1 + z)) * hardCoreAvailableMean G S I z at hmean
  have hsum := hardCoreOccupiedMass_add_complement G S I hIS z
  linarith

/-- For any vertex weights, a bipartition has an independent side carrying
at least half of the total weight. No positivity assumption is needed. -/
theorem exists_independent_half_weight_of_isBipartite
    (G : SimpleGraph V) (hG : G.IsBipartite) (S : Finset V) (w : V → ℝ) :
    ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet (I : Set V) ∧
      (∑ v ∈ S, w v) / 2 ≤ ∑ v ∈ I, w v := by
  classical
  obtain ⟨c⟩ := hG
  let I := S.filter (fun v => (c v).val = 0)
  have hIS : I ⊆ S := filter_subset _ _
  have hI : G.IsIndepSet (I : Set V) := by
    intro v hv u hu _ hAdj
    apply c.valid hAdj
    apply Fin.ext
    have hv0 := (mem_filter.mp hv).2
    have hu0 := (mem_filter.mp hu).2
    omega
  have hY : G.IsIndepSet ((S \ I : Finset V) : Set V) := by
    intro v hv u hu _ hAdj
    apply c.valid hAdj
    apply Fin.ext
    have hv0 : (c v).val ≠ 0 := by
      intro hc
      exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1, hc⟩)
    have hu0 : (c u).val ≠ 0 := by
      intro hc
      exact (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1, hc⟩)
    have hv2 := (c v).isLt
    have hu2 := (c u).isLt
    omega
  have hsum : (∑ v ∈ I, w v) + (∑ v ∈ S \ I, w v) = ∑ v ∈ S, w v := by
    have hdis : Disjoint I (S \ I) := disjoint_left.mpr (by
      intro v hv hvs; exact (mem_sdiff.mp hvs).2 hv)
    rw [← sum_union hdis, union_sdiff_of_subset hIS]
  by_cases hhalf : (∑ v ∈ S, w v) / 2 ≤ ∑ v ∈ I, w v
  · exact ⟨I, hIS, hI, hhalf⟩
  · refine ⟨S \ I, sdiff_subset, hY, ?_⟩
    linarith

theorem exists_independent_half_occupation_mass_of_isBipartite
    (G : SimpleGraph V) (hG : G.IsBipartite) (S : Finset V) (z : ℝ) :
    ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet (I : Set V) ∧
      hardCoreMean G S z / 2 ≤ hardCoreOccupiedMass G S I z := by
  rw [hardCoreMean_eq_sum_vertex_marginals]
  exact exists_independent_half_weight_of_isBipartite G hG S (hardCoreVertexMarginal G S z)

theorem hardCoreVariance_ge_half_mean_div_one_add_of_isBipartite
    (G : SimpleGraph V) (hG : G.IsBipartite) (S : Finset V)
    {z : ℝ} (hz : 0 < z) :
    hardCoreMean G S z / (2 * (1 + z)) ≤ hardCoreVariance G S z := by
  obtain ⟨I, hIS, hI, hhalf⟩ := exists_independent_half_weight_of_isBipartite G hG S
    (hardCoreVertexMarginal G S z)
  change hardCoreOccupiedMass G S S z / 2 ≤ hardCoreOccupiedMass G S I z at hhalf
  rw [← hardCoreMean_eq_sum_vertex_marginals G S z,
    hardCoreOccupiedMass_eq_activity_available_mean G S I hIS hI hz] at hhalf
  have hb := hardCoreVariance_ge_binomial_available_mean G S I hIS hI hz
  have hcomp : 1 - z / (1 + z) = 1 / (1 + z) := by field_simp; ring
  have hc : 0 ≤ 1 - z / (1 + z) := by rw [hcomp]; positivity
  have hm := mul_le_mul_of_nonneg_left hhalf hc
  have heq : (1 - z / (1 + z)) * (hardCoreMean G S z / 2) =
      hardCoreMean G S z / (2 * (1 + z)) := by rw [hcomp]; field_simp
  rw [heq] at hm
  calc
    hardCoreMean G S z / (2 * (1 + z)) ≤
        (1 - z / (1 + z)) * ((z / (1 + z)) * hardCoreAvailableMean G S I z) := hm
    _ = (z / (1 + z)) * (1 - z / (1 + z)) * hardCoreAvailableMean G S I z := by ring
    _ ≤ hardCoreVariance G S z := hb

theorem hardCoreVariance_ge_half_mean_div_one_add_of_isAcyclic
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    {z : ℝ} (hz : 0 < z) :
    hardCoreMean G S z / (2 * (1 + z)) ≤ hardCoreVariance G S z :=
  hardCoreVariance_ge_half_mean_div_one_add_of_isBipartite G hG.isBipartite S hz

#print axioms hardCoreMean_eq_sum_vertex_marginals
#print axioms hardCoreOccupiedMass_eq_activity_available_mean
#print axioms exists_independent_half_weight_of_isBipartite
#print axioms hardCoreVariance_ge_half_mean_div_one_add_of_isBipartite
#print axioms hardCoreVariance_ge_half_mean_div_one_add_of_isAcyclic

end ForestUnimodality
