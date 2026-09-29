import ForestUnimodality.CrossEdges
import ForestUnimodality.UnionBound

/-! Lower bounds for the number of independent one-vertex extensions,
retaining the actual number of edges in the ambient induced graph. -/

namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

theorem covered_singleton_eq_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (u : V) :
    Y \ available G Y {u} = Y.filter (G.Adj u) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨hxY, hxnot⟩ := mem_sdiff.mp hx
    apply mem_filter.mpr
    refine ⟨hxY, ?_⟩
    by_contra hnot
    apply hxnot
    apply mem_available.mpr
    refine ⟨hxY, ?_⟩
    intro w hw hxw
    have hwu := mem_singleton.mp hw
    subst w
    exact hnot hxw.symm
  · intro hx
    obtain ⟨hxY, hux⟩ := mem_filter.mp hx
    apply mem_sdiff.mpr
    refine ⟨hxY, ?_⟩
    intro hxA
    exact (mem_available.mp hxA).2 u (mem_singleton_self u) hux.symm

/-- A covered outside vertex consumes at least one edge, and edges incident
to an independent set are counted only once. -/
theorem available_complement_card_lower
    (G : SimpleGraph V) (Y K : Finset V) (hKY : K ⊆ Y)
    (hK : G.IsIndepSet (K : Set V)) :
    Y.card - K.card - edgeCountOn G Y ≤ (available G (Y \ K) K).card := by
  classical
  have hcov := covered_card_le_sum_singleton G (Y \ K) K
  have hsingle (u : V) : (Y \ K).card - (available G (Y \ K) {u}).card =
      ((Y \ K).filter (G.Adj u)).card := by
    rw [← card_sdiff_of_subset (available_subset G (Y \ K) {u}),
      covered_singleton_eq_neighbors]
  simp_rw [hsingle] at hcov
  have hsum : (∑ u ∈ K, ((Y \ K).filter (G.Adj u)).card) ≤
      ∑ u ∈ K, (Y.filter (G.Adj u)).card := by
    apply sum_le_sum
    intro u _
    apply card_le_card
    intro x hx
    obtain ⟨hxYK, hux⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨(mem_sdiff.mp hxYK).1, hux⟩
  have hbound := hcov.trans (hsum.trans (sum_neighbors_le_edgeCountOn_of_indep G Y K hKY hK))
  rw [card_sdiff_of_subset hKY] at hbound
  omega

/-- The extension incidence fiber is exactly the image of available outside
vertices under insertion. -/
theorem independentLayer_bipartiteAbove_eq_image_available
    (G : SimpleGraph V) (Y : Finset V) (k : ℕ) {K : Finset V}
    (hK : K ∈ independentLayer G Y k) :
    (independentLayer G Y (k + 1)).bipartiteAbove (fun A B : Finset V => A ⊆ B) K =
      (available G (Y \ K) K).image (fun u => insert u K) := by
  classical
  obtain ⟨hKY, hKI, hKc⟩ := mem_independentLayer.mp hK
  ext J
  constructor
  · intro hJ
    obtain ⟨hJL, hKJ⟩ := (mem_bipartiteAbove _).mp hJ
    obtain ⟨hJY, hJI, hJc⟩ := mem_independentLayer.mp hJL
    obtain ⟨u, huK, rfl⟩ := exists_eq_insert_iff.mpr ⟨hKJ, by omega⟩
    apply mem_image.mpr
    refine ⟨u, mem_available.mpr ⟨mem_sdiff.mpr ⟨hJY (mem_insert_self _ _), huK⟩, ?_⟩, rfl⟩
    intro w hw huw
    exact hJI (mem_insert_self _ _) (mem_insert_of_mem hw)
      (by intro he; subst w; exact huK hw) huw
  · intro hJ
    obtain ⟨u, huA, rfl⟩ := mem_image.mp hJ
    obtain ⟨huYK, hfree⟩ := mem_available.mp huA
    obtain ⟨huY, huK⟩ := mem_sdiff.mp huYK
    apply (mem_bipartiteAbove _).mpr
    refine ⟨mem_independentLayer.mpr ⟨insert_subset huY hKY, ?_, ?_⟩, subset_insert _ _⟩
    · intro x hx y hy hxy
      simp only [mem_coe, mem_insert] at hx hy
      rcases hx with rfl | hxK <;> rcases hy with rfl | hyK
      · exact (hxy rfl).elim
      · exact hfree y hyK
      · exact fun hxu => hfree x hxK hxu.symm
      · exact hKI hxK hyK hxy
    · simp [card_insert_of_notMem huK, hKc]

theorem independentLayer_bipartiteAbove_card_eq_available
    (G : SimpleGraph V) (Y : Finset V) (k : ℕ) {K : Finset V}
    (hK : K ∈ independentLayer G Y k) :
    ((independentLayer G Y (k + 1)).bipartiteAbove
      (fun A B : Finset V => A ⊆ B) K).card = (available G (Y \ K) K).card := by
  classical
  rw [independentLayer_bipartiteAbove_eq_image_available G Y k hK]
  apply card_image_of_injOn
  apply (insert_inj_on K).mono
  intro u hu
  exact (mem_sdiff.mp (mem_available.mp hu).1).2

/-- Nonnegative weights admit a reverse deletion bound using the actual
ambient edge count. An edge budget can subsequently weaken its multiplier. -/
theorem weighted_independent_extension_lower_bound
    (G : SimpleGraph V) (Y : Finset V) (k : ℕ) (f : Finset V → ℝ)
    (hf : ∀ K ∈ independentLayer G Y k, 0 ≤ f K) :
    ((Y.card - k - edgeCountOn G Y : ℕ) : ℝ) * ∑ K ∈ independentLayer G Y k, f K ≤
      ∑ J ∈ independentLayer G Y (k + 1), ∑ u ∈ J, f (J.erase u) := by
  classical
  rw [sum_erase_weights_eq_sum_extensions, mul_sum]
  apply sum_le_sum
  intro K hK
  apply mul_le_mul_of_nonneg_right _ (hf K hK)
  rw [independentLayer_bipartiteAbove_card_eq_available G Y k hK]
  obtain ⟨hKY, hKI, hKc⟩ := mem_independentLayer.mp hK
  have hb := available_complement_card_lower G Y K hKY hKI
  rw [hKc] at hb
  exact_mod_cast hb

#print axioms available_complement_card_lower
#print axioms independentLayer_bipartiteAbove_eq_image_available
#print axioms weighted_independent_extension_lower_bound
end ForestUnimodality
