import ForestUnimodality.TreeTerminalDecomposition

/-!
Pruning an actual terminal spider inside a larger host. All minimality
hypotheses are applied to subsets of the entire ambient vertex set `S`.
The terminal spider itself is never assumed to be a minimal counterexample.
-/

namespace ForestUnimodality

open Finset

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

theorem IsTerminalSpiderOn.block_subset {G : SimpleGraph V} {S H T : Finset V}
    {c p : V} {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) : T ⊆ S := by
  rw [h.vertices]
  exact subset_union_right

theorem IsTerminalSpiderOn.host_subset {G : SimpleGraph V} {S H T : Finset V}
    {c p : V} {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) : H ⊆ S := by
  rw [h.vertices]
  exact subset_union_left

theorem IsTerminalSpiderOn.branch_subset_block {G : SimpleGraph V} {S H T : Finset V}
    {c p : V} {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) {i : ι} (hi : i ∈ s) :
    B i ⊆ T := by
  intro x hx
  rw [h.spider.vertices]
  exact mem_insert_of_mem (mem_biUnion.mpr ⟨i, hi, hx⟩)

theorem IsTerminalSpiderOn.tip_mem {G : SimpleGraph V} {S H T : Finset V}
    {c p : V} {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) {i : ι} (hi : i ∈ s) :
    tip i ∈ S :=
  h.block_subset (h.branch_subset_block hi ((h.spider.paths i hi).host_subset (mem_singleton_self _)))

/-- The unique attachment edge ends at the center, so it cannot give a
branch tip a second neighbor in the host. -/
theorem IsTerminalSpiderOn.tip_is_leaf {G : SimpleGraph V} {S H T : Finset V}
    {c p : V} {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) {i : ι} (hi : i ∈ s) :
    ∃ a ∈ S, G.Adj (tip i) a ∧ ∀ x ∈ S, G.Adj (tip i) x → x = a := by
  have htB : tip i ∈ B i := (h.spider.paths i hi).host_subset (mem_singleton_self _)
  have htT : tip i ∈ T := h.branch_subset_block hi htB
  have htc : tip i ≠ c := fun he => h.spider.center_not_mem i hi (he ▸ htB)
  obtain ⟨a, ha, hta, huniq⟩ := h.spider.tip_is_leaf hi
  refine ⟨a, h.block_subset ha, hta, ?_⟩
  intro x hx htx
  rw [h.vertices] at hx
  rcases mem_union.mp hx with hxH | hxT
  · exact (htc ((h.attachment.cross x hxH (tip i) htT).mp htx.symm).2).elim
  · exact huniq x hxT htx

/-- A leg is a pendant extension of the entire remaining graph, including
the external host, rather than only of the remaining spider. -/
theorem IsTerminalSpiderOn.leg_extension {G : SimpleGraph V} {S H T : Finset V}
    {c p : V} {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) {i : ι} (hi : i ∈ s) :
    PendantPathExtension G (S \ B i) c (length i) S (tip i) := by
  have hBS := (h.branch_subset_block hi).trans h.block_subset
  have hc : c ∈ S \ B i := mem_sdiff.mpr
    ⟨h.block_subset h.attachment.block_root_mem, h.spider.center_not_mem i hi⟩
  have hcross : ∀ x ∈ B i, ∀ y ∈ S \ B i,
      G.Adj x y ↔ x = root i ∧ y = c := by
    intro x hx y hy
    obtain ⟨hyS, hyB⟩ := mem_sdiff.mp hy
    rw [h.vertices] at hyS
    rcases mem_union.mp hyS with hyH | hyT
    · have hxy : ¬ G.Adj x y := by
        intro ha
        have hxc := ((h.attachment.cross y hyH x (h.branch_subset_block hi hx)).mp ha.symm).2
        exact h.spider.center_not_mem i hi (hxc ▸ hx)
      have hyc : y ≠ c := fun he => h.attachment.block_root_not_host (he ▸ hyH)
      simp only [hxy, hyc, and_false]
    · rw [h.spider.vertices] at hyT
      rcases mem_insert.mp hyT with rfl | hyT
      · simpa only [and_true, eq_self_iff_true, G.adj_comm] using h.spider.center_adj i hi x hx
      · obtain ⟨j, hj, hyj⟩ := mem_biUnion.mp hyT
        have hij : i ≠ j := fun he => hyB (he ▸ hyj)
        have hxy := h.spider.separated.no_edges i hi j hj hij x hx y hyj
        have hyc : y ≠ c := fun he => h.spider.center_not_mem j hj (he ▸ hyj)
        simp only [hxy, hyc, and_false]
  have hext := (h.spider.paths i hi).reverse_attach (S \ B i) c hc
    disjoint_sdiff_self_left hcross
  rw [sdiff_union_of_subset hBS] at hext
  have hp := h.spider.length_pos i hi
  convert hext using 1
  omega

theorem IsTerminalSpiderOn.leg_length_le_thirteen_of_minimal_adjustedMean_nonpos
    {G : SimpleGraph V} {S H T I : Finset V} {c p : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsTerminalSpiderOn G S c H T p s B root tip length)
    (hI : IsMaximumIndependentOn G S I) (hbad : adjustedMeanPotential G S I.card ≤ 0)
    (hsmaller : ∀ U : Finset V, U ⊆ S → U.card < S.card →
      ∀ K : Finset V, IsMaximumIndependentOn G U K → 0 ≤ adjustedMeanPotential G U K.card)
    {i : ι} (hi : i ∈ s) : length i ≤ 13 := by
  by_contra hn
  obtain ⟨A, v, hv⟩ := (h.leg_extension hi).suffix 14 (by omega)
  exact no_pendantPath_fourteen_of_adjustedMean_nonpos hI hbad hsmaller hv

/-- In a spider with an odd leg, omitting the center costs no independent
vertices. An even leg's tip can also be omitted without a further loss. -/
theorem IsSpiderOn.independenceNumber_delete_center_tip_of_mixed_parity
    {G : SimpleGraph V} {T : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G T c s B root tip length) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (heven : length i % 2 = 0) (hodd : length j % 2 = 1) :
    independenceNumberOn G ((T.erase c).erase (tip i)) = independenceNumberOn G T := by
  classical
  have hrootless : (∑ k ∈ s, independenceNumberOn G ((B k).erase (root k))) <
      ∑ k ∈ s, independenceNumberOn G (B k) := by
    apply sum_lt_sum
    · intro k _
      exact (independenceNumberOn_erase_bounds G (B k) (root k)).1
    · refine ⟨j, hj, ?_⟩
      have hp := h.branch_alpha_pair hj
      have h1 := congrArg Prod.fst hp
      have h2 := congrArg Prod.snd hp
      dsimp at h1 h2
      omega
  have hAlpha : independenceNumberOn G T = ∑ k ∈ s, independenceNumberOn G (B k) := by
    rw [h.toIsRootedFanOn.independenceNumber, max_eq_left (by omega)]
  have htip : tip i ∈ B i := (h.paths i hi).host_subset (mem_singleton_self _)
  have hsets : (T.erase c).erase (tip i) = s.biUnion (fun k => (B k).erase (tip i)) := by
    rw [h.toIsRootedFanOn.erase_center]
    ext x
    simp only [mem_erase, mem_biUnion]
    constructor
    · rintro ⟨hne, k, hk, hxk⟩
      exact ⟨k, hk, hne, hxk⟩
    · rintro ⟨k, hk, hne, hxk⟩
      exact ⟨hne, k, hk, hxk⟩
  rw [hsets, hAlpha, (h.separated.subsets (fun k _ => erase_subset _ _)).independenceNumber_biUnion]
  apply sum_congr rfl
  intro k hk
  by_cases hki : k = i
  · subst k
    rw [h.branch_delete_tip_alpha hi]
    have hp := congrArg Prod.fst (h.branch_alpha_pair hi)
    dsimp at hp
    omega
  · have hnot : tip i ∉ B k := fun htk =>
      disjoint_left.mp (h.separated.disjoint i hi k hk (fun heq => hki heq.symm)) htip htk
    rw [erase_eq_of_notMem hnot]

/-- The parity exchange is valid in the full host-plus-spider graph. It
produces an actual maximum independent set of `S` omitting an even tip. -/
theorem IsTerminalSpiderOn.exists_maximum_omitting_even_tip_of_odd_leg
    {G : SimpleGraph V} {S H T : Finset V} {c p : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (heven : length i % 2 = 0) (hodd : length j % 2 = 1) :
    ∃ K : Finset V, IsMaximumIndependentOn G S K ∧ tip i ∉ K := by
  let U := (T.erase c).erase (tip i)
  have hUsub : U ⊆ T := (erase_subset _ _).trans (erase_subset _ _)
  have hUS : H ∪ U ⊆ S := by
    rw [h.vertices]
    exact union_subset_union (Subset.refl _) hUsub
  have hAlphaU : independenceNumberOn G U = independenceNumberOn G T :=
    h.spider.independenceNumber_delete_center_tip_of_mixed_parity hi hj heven hodd
  have hAlphaHU : independenceNumberOn G (H ∪ U) = independenceNumberOn G S := by
    have he := independenceNumberOn_disjoint_union G H U
      (h.attachment.disjoint.mono (Subset.refl _) hUsub)
      (fun x hx y hy => h.attachment.no_edges_deleted_block x hx y (mem_of_mem_erase hy))
    rw [hAlphaU] at he
    have hle := h.attachment.independenceNumber_eq
    rw [← h.vertices] at hle
    have hmono := independenceNumberOn_mono G hUS
    omega
  obtain ⟨K, hK⟩ := exists_maximumIndependentOn G (H ∪ U)
  have hcard : K.card = independenceNumberOn G S :=
    hK.card_eq_independenceNumberOn.trans hAlphaHU
  refine ⟨K, ⟨mem_independentSubsets.mpr ⟨hK.subset.trans hUS, hK.independent⟩, ?_⟩, ?_⟩
  · intro L hL
    rw [hcard]
    exact Finset.le_sup hL
  · intro htK
    rcases mem_union.mp (hK.subset htK) with htH | htU
    · exact disjoint_left.mp h.attachment.disjoint htH
        (h.branch_subset_block hi ((h.spider.paths i hi).host_subset (mem_singleton_self _)))
    · exact (mem_erase.mp htU).1 rfl

theorem IsTerminalSpiderOn.same_parity_of_tips_forced
    {G : SimpleGraph V} {S H T : Finset V} {c p : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsTerminalSpiderOn G S c H T p s B root tip length)
    (hforced : ∀ K : Finset V, IsMaximumIndependentOn G S K → ∀ i ∈ s, tip i ∈ K) :
    ∀ i ∈ s, ∀ j ∈ s, length i % 2 = length j % 2 := by
  intro i hi j hj
  by_contra hne
  have hai := Nat.mod_lt (length i) (by decide : 0 < 2)
  have haj := Nat.mod_lt (length j) (by decide : 0 < 2)
  have hc : (length i % 2 = 0 ∧ length j % 2 = 1) ∨
      (length j % 2 = 0 ∧ length i % 2 = 1) := by omega
  rcases hc with ⟨hei, hoj⟩ | ⟨hej, hoi⟩
  · obtain ⟨K, hK, ht⟩ := h.exists_maximum_omitting_even_tip_of_odd_leg hi hj hei hoj
    exact ht (hforced K hK i hi)
  · obtain ⟨K, hK, ht⟩ := h.exists_maximum_omitting_even_tip_of_odd_leg hj hi hej hoi
    exact ht (hforced K hK j hj)

theorem IsTerminalSpiderOn.tips_mem_of_minimal_adjustedMean_nonpos
    {G : SimpleGraph V} {S H T I : Finset V} {c p : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsTerminalSpiderOn G S c H T p s B root tip length)
    (hI : IsMaximumIndependentOn G S I) (hbad : adjustedMeanPotential G S I.card ≤ 0)
    (hsmaller : ∀ U : Finset V, U ⊆ S → U.card < S.card →
      ∀ K : Finset V, IsMaximumIndependentOn G U K → 0 ≤ adjustedMeanPotential G U K.card) :
    ∀ K : Finset V, IsMaximumIndependentOn G S K → ∀ i ∈ s, tip i ∈ K := by
  intro K hK i hi
  have hbadK : adjustedMeanPotential G S K.card ≤ 0 := by
    rw [hK.card_eq_independenceNumberOn, ← hI.card_eq_independenceNumberOn]
    exact hbad
  obtain ⟨a, _, _, hleaf⟩ := h.tip_is_leaf hi
  exact hK.leaf_mem_of_adjustedMean_nonpos hbadK hsmaller (h.tip_mem hi) hleaf

theorem IsTerminalSpiderOn.same_parity_of_minimal_adjustedMean_nonpos
    {G : SimpleGraph V} {S H T I : Finset V} {c p : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsTerminalSpiderOn G S c H T p s B root tip length)
    (hI : IsMaximumIndependentOn G S I) (hbad : adjustedMeanPotential G S I.card ≤ 0)
    (hsmaller : ∀ U : Finset V, U ⊆ S → U.card < S.card →
      ∀ K : Finset V, IsMaximumIndependentOn G U K → 0 ≤ adjustedMeanPotential G U K.card) :
    ∀ i ∈ s, ∀ j ∈ s, length i % 2 = length j % 2 :=
  h.same_parity_of_tips_forced (h.tips_mem_of_minimal_adjustedMean_nonpos hI hbad hsmaller)

#print axioms IsTerminalSpiderOn.tip_is_leaf
#print axioms IsTerminalSpiderOn.leg_extension
#print axioms IsTerminalSpiderOn.leg_length_le_thirteen_of_minimal_adjustedMean_nonpos
#print axioms IsSpiderOn.independenceNumber_delete_center_tip_of_mixed_parity
#print axioms IsTerminalSpiderOn.exists_maximum_omitting_even_tip_of_odd_leg
#print axioms IsTerminalSpiderOn.tips_mem_of_minimal_adjustedMean_nonpos
#print axioms IsTerminalSpiderOn.same_parity_of_minimal_adjustedMean_nonpos

end ForestUnimodality
