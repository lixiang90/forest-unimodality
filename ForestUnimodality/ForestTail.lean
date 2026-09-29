import ForestUnimodality.ForestIndependenceBound
import ForestUnimodality.ExtensionCounts

/-!
A universal decreasing-tail bound for independent-set counts of forests.
The available vertices outside an independent set induce a forest. A large
independent subset of those vertices can be joined to the original set,
which bounds their number using the maximum independent-set cardinality.
Double counting one-vertex extensions then gives the coefficient inequality.
-/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- At most twice the remaining independence capacity many vertices can be
adjoined individually to an independent set in a forest. -/
theorem IsMaximumIndependentOn.card_available_complement_le
    {G : SimpleGraph V} {S I J : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic)
    (hJ : J ∈ independentSubsets G S) :
    (available G (S \ J) J).card ≤ 2 * (I.card - J.card) := by
  classical
  obtain ⟨K, hK, hhalf⟩ := exists_independentSubsets_card_bound_of_isAcyclic G hG
    (available G (S \ J) J)
  obtain ⟨hJS, hJI⟩ := mem_independentSubsets.mp hJ
  obtain ⟨hKA, hKI⟩ := mem_independentSubsets.mp hK
  have hKS : K ⊆ S \ J := hKA.trans (available_subset G (S \ J) J)
  have hKoutside : K ∈ independentSubsets G (S \ J) :=
    mem_independentSubsets.mpr ⟨hKS, hKI⟩
  have hJA : J ⊆ available G J K := by
    intro j hj
    apply mem_available.mpr
    refine ⟨hj, ?_⟩
    intro w hw hadj
    exact (mem_available.mp (hKA hw)).2 j hj hadj.symm
  have hjoin : K ∪ J ∈ independentSubsets G S := join_mem hJS hJI hKoutside hJA
  have hdis : Disjoint K J := by
    apply disjoint_left.mpr
    intro w hwK hwJ
    exact (mem_sdiff.mp (hKS hwK)).2 hwJ
  have hbound := hI.2 _ hjoin
  rw [card_union_of_disjoint hdis] at hbound
  have hremaining : K.card ≤ I.card - J.card := by omega
  exact hhalf.trans (Nat.mul_le_mul_left 2 hremaining)

/-- The forest extension bound holds at every degree, including degrees beyond
the maximum independent-set cardinality. -/
theorem IsMaximumIndependentOn.countIndependent_forest_extension_bound
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic) (k : ℕ) :
    (k + 1) * countIndependent G S (k + 1) ≤
      2 * (I.card - k) * countIndependent G S k := by
  classical
  have h := Finset.card_mul_le_card_mul' (s := independentLayer G S k)
    (t := independentLayer G S (k + 1)) (fun A B : Finset V => A ⊆ B)
    (n := k + 1) (m := 2 * (I.card - k)) ?_ ?_
  · simpa only [card_independentLayer, mul_comm] using h
  · intro J hJ
    obtain ⟨hJS, hJI, hJc⟩ := mem_independentLayer.mp hJ
    rw [← hJc, ← Finset.card_image_of_injOn J.erase_injOn]
    apply Finset.card_le_card
    intro K hK
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hK
    apply (Finset.mem_bipartiteBelow _).mpr
    refine ⟨mem_independentLayer.mpr ⟨(erase_subset v J).trans hJS,
      hJI.mono (Finset.coe_subset.mpr (erase_subset v J)), ?_⟩, erase_subset v J⟩
    have hc := card_erase_add_one hv
    omega
  · intro K hK
    obtain ⟨hKS, hKI, hKc⟩ := mem_independentLayer.mp hK
    calc
      ((independentLayer G S (k + 1)).bipartiteAbove
          (fun A B : Finset V => A ⊆ B) K).card ≤
          ((available G (S \ K) K).image fun v => insert v K).card := by
        apply Finset.card_le_card
        intro J hJ
        obtain ⟨hJL, hKJ⟩ := (mem_bipartiteAbove _).mp hJ
        obtain ⟨hJS, hJI, hJc⟩ := mem_independentLayer.mp hJL
        have hc : J.card = K.card + 1 := by omega
        obtain ⟨v, hvK, rfl⟩ := Finset.exists_eq_insert_iff.mpr ⟨hKJ, hc.symm⟩
        refine mem_image.mpr ⟨v, ?_, rfl⟩
        apply mem_available.mpr
        refine ⟨mem_sdiff.mpr ⟨hJS (mem_insert_self v K), hvK⟩, ?_⟩
        intro w hw
        exact hJI (mem_insert_self v K) (mem_insert_of_mem hw)
          (by intro he; subst w; exact hvK hw)
      _ ≤ (available G (S \ K) K).card := card_image_le
      _ ≤ 2 * (I.card - k) := by
        have hb := hI.card_available_complement_le hG
          (mem_independentSubsets.mpr ⟨hKS, hKI⟩)
        simpa only [hKc] using hb

/-- Beyond the universal forest cutoff, successive independent-set counts
are nonincreasing. The arithmetic condition is valid without a size guard. -/
theorem IsMaximumIndependentOn.countIndependent_succ_le_of_forest_tail
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic)
    (k : ℕ) (htail : 2 * I.card ≤ 3 * k + 1) :
    countIndependent G S (k + 1) ≤ countIndependent G S k := by
  have h := hI.countIndependent_forest_extension_bound hG k
  have hfactor : 2 * (I.card - k) ≤ k + 1 := by omega
  have hb := h.trans (Nat.mul_le_mul_right (countIndependent G S k) hfactor)
  exact Nat.le_of_mul_le_mul_left hb (by omega)

/-- The manuscript's cutoff floor((2a+1)/3) implies the tail condition. -/
theorem IsMaximumIndependentOn.countIndependent_succ_le_of_cutoff
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic)
    (k : ℕ) (hk : (2 * I.card + 1) / 3 ≤ k) :
    countIndependent G S (k + 1) ≤ countIndependent G S k := by
  apply hI.countIndependent_succ_le_of_forest_tail hG k
  omega

#print axioms IsMaximumIndependentOn.card_available_complement_le
#print axioms IsMaximumIndependentOn.countIndependent_forest_extension_bound
#print axioms IsMaximumIndependentOn.countIndependent_succ_le_of_forest_tail
#print axioms IsMaximumIndependentOn.countIndependent_succ_le_of_cutoff

end ForestUnimodality
