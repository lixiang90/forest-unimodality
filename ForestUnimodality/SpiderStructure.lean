import ForestUnimodality.SpiderMean
import ForestUnimodality.PathPruning

/-! Structural properties of actual spiders, independent of numerical
certificates: removing the first endpoint of a real path leaves a real
path, and incompatible leg parities permit a maximum set omitting a tip. -/
namespace ForestUnimodality
open Finset
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

/-- Remove the entire original host from a nontrivial pendant extension.
The remaining new vertices form an actual path from a singleton host. -/
theorem PendantPathExtension.remove_host {G : SimpleGraph V} {H S : Finset V}
    {v u : V} {n : ℕ} (h : PendantPathExtension G H v n S u) (hn : 0 < n) :
    ∃ w : V, PendantPathExtension G {w} w (n - 1) (S \ H) u := by
  induction h with
  | zero _ => omega
  | @succ n S u h w hw hadj ih =>
    cases n with
    | zero =>
      cases h with
      | zero hv =>
        have he : insert w H \ H = ({w} : Finset V) := by
          ext x
          simp only [mem_sdiff, mem_insert, mem_singleton]
          constructor
          · rintro ⟨h | h, hn⟩
            · exact h
            · exact (hn h).elim
          · rintro rfl
            exact ⟨Or.inl rfl, hw⟩
        refine ⟨w, ?_⟩
        rw [he]
        exact PendantPathExtension.zero (mem_singleton_self w)
    | succ n =>
      obtain ⟨t, ht⟩ := ih (by omega)
      have hwH : w ∉ H := fun hw' => hw (h.host_subset hw')
      have hw' : w ∉ S \ H := fun hw' => hw (mem_sdiff.mp hw').1
      have hadj' : ∀ x ∈ S \ H, G.Adj w x ↔ x = u :=
        fun x hx => hadj x (mem_sdiff.mp hx).1
      have hs : insert w (S \ H) = insert w S \ H := by
        ext x
        simp only [mem_insert, mem_sdiff]
        constructor
        · rintro (rfl | ⟨hxS, hxH⟩)
          · exact ⟨Or.inl rfl, hwH⟩
          · exact ⟨Or.inr hxS, hxH⟩
        · rintro ⟨rfl | hxS, hxH⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hxS, hxH⟩
      refine ⟨t, ?_⟩
      have hext := PendantPathExtension.succ ht w hw' hadj'
      simpa only [Nat.add_sub_cancel, Nat.succ_sub_one, hs] using hext

theorem PendantPathExtension.initial_delete_alpha {G : SimpleGraph V}
    {S : Finset V} {v u : V} {n : ℕ}
    (h : PendantPathExtension G {v} v n S u) :
    independenceNumberOn G (S.erase v) = (n + 1) / 2 := by
  by_cases hn : n = 0
  · subst n
    cases h with
    | zero _ => simp [independenceNumberOn, independentSubsets_empty_eq_singleton]
  · obtain ⟨w, hw⟩ := h.remove_host (by omega)
    have ht := hw.card_transfer
    rw [independenceNumberOn_singleton] at ht
    have he : independenceNumberOn G ∅ = 0 := by
      simp [independenceNumberOn, independentSubsets_empty_eq_singleton]
    simp only [erase_singleton, he] at ht
    rw [pathCardTransfer_from_singleton] at ht
    have hf := congrArg Prod.fst ht
    have hs : S \ {v} = S.erase v := sdiff_singleton_eq_erase _ _
    rw [hs] at hf
    convert hf using 1
    omega

omit [DecidableEq ι] in
theorem IsSpiderOn.branch_delete_tip_alpha {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) {i : ι} (hi : i ∈ s) :
    independenceNumberOn G ((B i).erase (tip i)) = length i / 2 := by
  have ht := (h.paths i hi).initial_delete_alpha
  have hp := h.length_pos i hi
  convert ht using 1
  omega

/-- A mixed even/odd spider has an actual maximum independent set omitting
the tip of any selected even leg. Thus forced inclusion of all leaf tips
excludes mixed parity by a real graph argument. -/
theorem IsSpiderOn.exists_maximum_omitting_even_tip_of_odd_leg
    {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (heven : length i % 2 = 0) (hodd : length j % 2 = 1) :
    ∃ K : Finset V, IsMaximumIndependentOn G S K ∧ tip i ∉ K := by
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
  have hAlpha : independenceNumberOn G S = ∑ k ∈ s, independenceNumberOn G (B k) := by
    rw [h.toIsRootedFanOn.independenceNumber, max_eq_left (by omega)]
  have htip : tip i ∈ B i := (h.paths i hi).host_subset (mem_singleton_self _)
  let T := s.biUnion fun k => (B k).erase (tip i)
  have hTS : T ⊆ S := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := mem_biUnion.mp hx
    rw [h.vertices]
    exact mem_insert_of_mem (mem_biUnion.mpr ⟨k, hk, (mem_erase.mp hxk).2⟩)
  have htT : tip i ∉ T := by
    intro ht
    obtain ⟨k, _, htk⟩ := mem_biUnion.mp ht
    exact (mem_erase.mp htk).1 rfl
  have hTalpha : independenceNumberOn G T = independenceNumberOn G S := by
    rw [hAlpha, (h.separated.subsets (fun k _ => erase_subset _ _)).independenceNumber_biUnion]
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
  obtain ⟨K, hK⟩ := exists_maximumIndependentOn G T
  have hcard : K.card = independenceNumberOn G S := hK.card_eq_independenceNumberOn.trans hTalpha
  refine ⟨K, ⟨mem_independentSubsets.mpr ⟨hK.subset.trans hTS, hK.independent⟩, ?_⟩,
    fun htk => htT (hK.subset htk)⟩
  intro L hL
  rw [hcard]
  exact Finset.le_sup hL

theorem PendantPathExtension.endpoint_ne_root {G : SimpleGraph V} {H S : Finset V}
    {v u : V} {n : ℕ} (h : PendantPathExtension G H v n S u) (hn : 0 < n) : u ≠ v := by
  cases h with
  | zero _ => omega
  | succ hp w hw _ =>
    intro he
    apply hw
    rw [he]
    exact hp.host_subset hp.root_mem

theorem PendantPathExtension.eq_of_zero {G : SimpleGraph V} {H S : Finset V}
    {v u : V} (h : PendantPathExtension G H v 0 S u) : S = H ∧ u = v := by
  cases h
  exact ⟨rfl, rfl⟩

/-- The starting vertex of a nontrivial path really has exactly one
neighbor inside the constructed path; this is not a message assumption. -/
theorem PendantPathExtension.initial_leaf {G : SimpleGraph V} {S : Finset V}
    {v u : V} {n : ℕ} (h : PendantPathExtension G {v} v n S u) (hn : 0 < n) :
    ∃ a ∈ S, G.Adj v a ∧ ∀ x ∈ S, G.Adj v x → x = a := by
  induction h with
  | zero _ => omega
  | @succ n S u h w hw hadj ih =>
    cases n with
    | zero =>
      cases h with
      | zero hv =>
        refine ⟨w, mem_insert_self _ _, (hadj v (mem_singleton_self _)).mpr rfl |>.symm, ?_⟩
        intro x hx hxadj
        rcases mem_insert.mp hx with hxe | hxv
        · exact hxe
        · have hxv' := mem_singleton.mp hxv
          exact (G.irrefl (hxv' ▸ hxadj)).elim
    | succ n =>
      obtain ⟨a, ha, hva, huniq⟩ := ih (by omega)
      have hvS : v ∈ S := h.host_subset (mem_singleton_self _)
      have hne := h.endpoint_ne_root (by omega)
      refine ⟨a, mem_insert_of_mem ha, hva, ?_⟩
      intro x hx hvx
      rcases mem_insert.mp hx with rfl | hx
      · have hvu := (hadj v hvS).mp hvx.symm
        exact (hne hvu.symm).elim
      · exact huniq x hx hvx

omit [DecidableEq ι] in
/-- Every specified spider tip is an actual leaf of the whole graph. -/
theorem IsSpiderOn.tip_is_leaf {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) {i : ι} (hi : i ∈ s) :
    ∃ a ∈ S, G.Adj (tip i) a ∧ ∀ x ∈ S, G.Adj (tip i) x → x = a := by
  have htB : tip i ∈ B i := (h.paths i hi).host_subset (mem_singleton_self _)
  have hBinS : B i ⊆ S := by
    intro x hx
    rw [h.vertices]
    exact mem_insert_of_mem (mem_biUnion.mpr ⟨i, hi, hx⟩)
  have hother : ∀ j ∈ s, j ≠ i → ∀ x ∈ B j, ¬ G.Adj (tip i) x := by
    intro j hj hji x hx
    exact h.separated.no_edges i hi j hj (fun he => hji he.symm) (tip i) htB x hx
  by_cases hn : length i - 1 = 0
  · have hp := h.paths i hi
    rw [hn] at hp
    have hB : B i = {tip i} := hp.eq_of_zero.1
    have hr : root i = tip i := hp.eq_of_zero.2
    refine ⟨c, h.toIsRootedFanOn.center_mem, ?_, ?_⟩
    · exact ((h.center_adj i hi (tip i) htB).mpr hr.symm).symm
    · intro x hx htx
      rw [h.vertices] at hx
      rcases mem_insert.mp hx with hxc | hx
      · exact hxc
      · obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp hx
        by_cases hji : j = i
        · subst j
          rw [hB] at hxj
          have hxv := mem_singleton.mp hxj
          exact (G.irrefl (hxv ▸ htx)).elim
        · exact (hother j hj hji x hxj htx).elim
  · obtain ⟨a, ha, hta, huniq⟩ := (h.paths i hi).initial_leaf (by omega)
    have hne := (h.paths i hi).endpoint_ne_root (by omega)
    refine ⟨a, hBinS ha, hta, ?_⟩
    intro x hx htx
    rw [h.vertices] at hx
    rcases mem_insert.mp hx with rfl | hx
    · have htr := (h.center_adj i hi (tip i) htB).mp htx.symm
      exact (hne htr.symm).elim
    · obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp hx
      by_cases hji : j = i
      · subst j
        exact huniq x hxj htx
      · exact (hother j hj hji x hxj htx).elim

theorem IsSpiderOn.same_parity_of_tips_forced {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length)
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

/-- Actual same-parity restriction for a spider which is a minimal
nonpositive adjusted-mean counterexample. It derives tip inclusion from
the already-proved leaf pruning theorem, rather than assuming it. -/
theorem IsSpiderOn.same_parity_of_minimal_adjustedMean_nonpos
    {G : SimpleGraph V} {S I : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) (hI : IsMaximumIndependentOn G S I)
    (hbad : adjustedMeanPotential G S I.card ≤ 0)
    (hsmaller : ∀ T : Finset V, T ⊆ S → T.card < S.card →
      ∀ K : Finset V, IsMaximumIndependentOn G T K → 0 ≤ adjustedMeanPotential G T K.card) :
    ∀ i ∈ s, ∀ j ∈ s, length i % 2 = length j % 2 := by
  apply h.same_parity_of_tips_forced
  intro K hK i hi
  have hbadK : adjustedMeanPotential G S K.card ≤ 0 := by
    rw [hK.card_eq_independenceNumberOn, ← hI.card_eq_independenceNumberOn]
    exact hbad
  have htipS : tip i ∈ S := by
    rw [h.vertices]
    exact mem_insert_of_mem (mem_biUnion.mpr ⟨i, hi,
      (h.paths i hi).host_subset (mem_singleton_self _)⟩)
  obtain ⟨a, _, _, hleaf⟩ := h.tip_is_leaf hi
  exact hK.leaf_mem_of_adjustedMean_nonpos hbadK hsmaller htipS hleaf

/-- Concatenate two actual pendant extensions. -/
theorem PendantPathExtension.trans {G : SimpleGraph V} {H T S : Finset V}
    {v w u : V} {n m : ℕ} (h : PendantPathExtension G H v n T w)
    (ht : PendantPathExtension G T w m S u) : PendantPathExtension G H v (n + m) S u := by
  induction ht with
  | zero _ => simpa only [Nat.add_zero] using h
  | succ hp x hx hadj ih =>
    simpa only [Nat.add_assoc] using PendantPathExtension.succ ih x hx hadj

/-- A path specified from its distant tip towards its connection root can
be attached in reverse order to an arbitrary actual host. The only edge
between the two vertex sets is the designated root-to-host edge. -/
theorem PendantPathExtension.reverse_attach {G : SimpleGraph V} {B : Finset V}
    {tip root : V} {n : ℕ} (hp : PendantPathExtension G {tip} tip n B root)
    (H : Finset V) (c : V) (hc : c ∈ H) (hd : Disjoint H B)
    (hcross : ∀ x ∈ B, ∀ y ∈ H, G.Adj x y ↔ x = root ∧ y = c) :
    PendantPathExtension G H c (n + 1) (H ∪ B) tip := by
  induction hp generalizing H c with
  | zero ht =>
    have htip : tip ∉ H := fun htH => disjoint_left.mp hd htH (mem_singleton_self _)
    have hadj : ∀ y ∈ H, G.Adj tip y ↔ y = c := by
      intro y hy
      simpa only [true_and, eq_self_iff_true] using hcross tip (mem_singleton_self _) y hy
    have hext := PendantPathExtension.succ (PendantPathExtension.zero hc) tip htip hadj
    simpa only [union_singleton] using hext
  | @succ n B u hp w hw hadj ih =>
    have hwH : w ∉ H := fun hwH => disjoint_left.mp hd hwH (mem_insert_self _ _)
    have hd' : Disjoint (insert w H) B := by
      apply disjoint_left.mpr
      intro x hx hxB
      rcases mem_insert.mp hx with rfl | hxH
      · exact hw hxB
      · exact disjoint_left.mp hd hxH (mem_insert_of_mem hxB)
    have hcross' : ∀ x ∈ B, ∀ y ∈ insert w H, G.Adj x y ↔ x = u ∧ y = w := by
      intro x hx y hy
      rcases mem_insert.mp hy with rfl | hyH
      · have he := hadj x hx
        simpa only [and_true, eq_self_iff_true, G.adj_comm] using he
      · have hxy : ¬ G.Adj x y := by
          intro ha
          have hxw := ((hcross x (mem_insert_of_mem hx) y hyH).mp ha).1
          exact hw (hxw ▸ hx)
        have hyw : y ≠ w := fun he => hwH (he ▸ hyH)
        simp only [hxy, hyw, and_false]
    have htail := ih (insert w H) w (mem_insert_self _ _) hd' hcross'
    have hfirstAdj : ∀ y ∈ H, G.Adj w y ↔ y = c := by
      intro y hy
      simpa only [true_and, eq_self_iff_true] using hcross w (mem_insert_self _ _) y hy
    have hfirst := PendantPathExtension.succ (PendantPathExtension.zero hc) w hwH hfirstAdj
    have hext := hfirst.trans htail
    have hsets : insert w H ∪ B = H ∪ insert w B := by
      ext x
      simp only [mem_union, mem_insert]
      tauto
    rw [hsets] at hext
    convert hext using 1
    omega

omit [DecidableEq ι] in
/-- Each actual spider leg is a pendant extension of the whole remaining
graph, including its center and all other legs. -/
theorem IsSpiderOn.leg_extension {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) {i : ι} (hi : i ∈ s) :
    PendantPathExtension G (S \ B i) c (length i) S (tip i) := by
  have hBS : B i ⊆ S := by
    intro x hx
    rw [h.vertices]
    exact mem_insert_of_mem (mem_biUnion.mpr ⟨i, hi, hx⟩)
  have hc : c ∈ S \ B i := mem_sdiff.mpr
    ⟨h.toIsRootedFanOn.center_mem, h.center_not_mem i hi⟩
  have hd : Disjoint (S \ B i) (B i) := disjoint_sdiff_self_left
  have hcross : ∀ x ∈ B i, ∀ y ∈ S \ B i,
      G.Adj x y ↔ x = root i ∧ y = c := by
    intro x hx y hy
    obtain ⟨hyS, hyB⟩ := mem_sdiff.mp hy
    rw [h.vertices] at hyS
    rcases mem_insert.mp hyS with rfl | hyS
    · simpa only [and_true, eq_self_iff_true, G.adj_comm] using h.center_adj i hi x hx
    · obtain ⟨j, hj, hyj⟩ := mem_biUnion.mp hyS
      have hij : i ≠ j := fun he => hyB (he ▸ hyj)
      have hxy := h.separated.no_edges i hi j hj hij x hx y hyj
      have hyc : y ≠ c := fun he => h.center_not_mem j hj (he ▸ hyj)
      simp only [hxy, hyc, and_false]
  have hext := (h.paths i hi).reverse_attach (S \ B i) c hc hd hcross
  have hunion : (S \ B i) ∪ B i = S := sdiff_union_of_subset hBS
  rw [hunion] at hext
  have hp := h.length_pos i hi
  convert hext using 1
  omega

theorem IsSpiderOn.leg_length_le_thirteen_of_minimal_adjustedMean_nonpos
    {G : SimpleGraph V} {S I : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) (hI : IsMaximumIndependentOn G S I)
    (hbad : adjustedMeanPotential G S I.card ≤ 0)
    (hsmaller : ∀ T : Finset V, T ⊆ S → T.card < S.card →
      ∀ K : Finset V, IsMaximumIndependentOn G T K → 0 ≤ adjustedMeanPotential G T K.card)
    {i : ι} (hi : i ∈ s) : length i ≤ 13 := by
  by_contra hn
  obtain ⟨H, v, hv⟩ := (h.leg_extension hi).suffix 14 (by omega)
  exact no_pendantPath_fourteen_of_adjustedMean_nonpos hI hbad hsmaller hv

#print axioms PendantPathExtension.remove_host
#print axioms IsSpiderOn.branch_delete_tip_alpha
#print axioms IsSpiderOn.exists_maximum_omitting_even_tip_of_odd_leg
#print axioms IsSpiderOn.tip_is_leaf
#print axioms IsSpiderOn.same_parity_of_minimal_adjustedMean_nonpos
#print axioms PendantPathExtension.reverse_attach
#print axioms IsSpiderOn.leg_extension
#print axioms IsSpiderOn.leg_length_le_thirteen_of_minimal_adjustedMean_nonpos
end ForestUnimodality
