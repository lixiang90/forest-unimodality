import ForestUnimodality.TerminalExceptionalBranches
import ForestUnimodality.SpiderStructure

/-! A terminal branch of type T33/T35 forces its actual host root into every
maximum independent set of a minimal nonpositive graph. -/
namespace ForestUnimodality
open Finset TerminalBlockRecurrence
universe u
variable {V : Type u} [DecidableEq V]

theorem InducedIso.BranchParameters.E_zero_identity {G : SimpleGraph V} {T : Finset V}
    {w : V} {i : Fin 8} (hp : InducedIso.BranchParameters G T w i) (X Y r : ℝ) :
    E (actualBlockState G T w) 0 X Y r =
      partitionFunction G (T.erase w) (2 : ℝ) *
        (60 * X + 60 * ((MeanTerminalClosure.branchRatio i.val : ℝ) - 1) * Y +
          60 * (MeanTerminalClosure.branchDeletedExcess i.val : ℝ) * (r - 1) +
          60 * (MeanTerminalClosure.branchRatio i.val : ℝ) * MeanTerminalClosure.branchExcess i.val -
          29 * ((MeanTerminalClosure.branchRatio i.val : ℝ) - 1)) := by
  have hZ := partitionFunction_pos G T (z := (2 : ℝ)) (by norm_num)
  have hA := partitionFunction_pos G (T.erase w) (z := (2 : ℝ)) (by norm_num)
  rw [← hp.ratio_eq, ← hp.deleted_excess_eq, ← hp.excess_eq]
  unfold E actualBlockState adjustedMeanPotential hardCoreMean
  field_simp [ne_of_gt hZ, ne_of_gt hA]
  ring

theorem InducedIso.BranchParameters.E_zero_pos {G : SimpleGraph V} {T : Finset V}
    {w : V} {i : Fin 8} (hp : InducedIso.BranchParameters G T w i) (hi : i = 0 ∨ i = 1)
    (X Y r : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hr : 1 ≤ r) :
    0 < E (actualBlockState G T w) 0 X Y r := by
  have hR : 1 ≤ (MeanTerminalClosure.branchRatio i.val : ℝ) := by
    rcases hi with rfl | rfl <;> norm_num [MeanTerminalClosure.branchRatio]
  have hB : 0 ≤ (MeanTerminalClosure.branchDeletedExcess i.val : ℝ) := by
    rcases hi with rfl | rfl <;> norm_num [MeanTerminalClosure.branchDeletedExcess]
  have hgain : 0 < 60 * (MeanTerminalClosure.branchRatio i.val : ℝ) *
      MeanTerminalClosure.branchExcess i.val - 29 * ((MeanTerminalClosure.branchRatio i.val : ℝ) - 1) := by
    rcases hi with rfl | rfl <;>
      norm_num [MeanTerminalClosure.branchRatio, MeanTerminalClosure.branchExcess]
  rw [hp.E_zero_identity]
  apply mul_pos (partitionFunction_pos G _ (by norm_num : (0 : ℝ) ≤ 2))
  have h1 := mul_nonneg (sub_nonneg.mpr hR) hY
  have h2 := mul_nonneg hB (sub_nonneg.mpr hr)
  nlinarith

theorem IsRootedBlockAttachment.host_rootDefect_eq_one_of_terminal_nonpos
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w) (hG : G.IsAcyclic)
    (hsmaller : GlobalSmallerMeanHyp.{u} (H ∪ T).card)
    {i : Fin 8} (hp : InducedIso.BranchParameters G T w i) (hi : i = 0 ∨ i = 1)
    (hbad : adjustedMeanPotential G (H ∪ T) (independenceNumberOn G (H ∪ T)) ≤ 0) :
    rootDefect G H v = 1 := by
  rcases rootDefect_zero_or_one G H v with he | he
  · have hc := card_union_of_disjoint h.disjoint
    have ht : 0 < T.card := card_pos.mpr ⟨w, h.block_root_mem⟩
    have hH := hsmaller V G H (by omega) hG
    have hJ := hsmaller V G (H.erase v)
      (lt_of_le_of_lt (card_le_card (erase_subset _ _)) (by omega)) hG
    have hr := (partitionFunction_delete_ratio_bounds G H h.host_root_mem
      (z := (2 : ℝ)) (by norm_num)).1
    have hX := mul_nonneg (show 0 ≤ partitionFunction G H (2 : ℝ) /
      partitionFunction G (H.erase v) 2 by linarith) hH
    have hpos := hp.E_zero_pos hi _ _ _ hX hJ hr
    have hpos' : 0 < adjustedMeanPotential G (H ∪ T) (independenceNumberOn G (H ∪ T)) := by
      apply h.adjustedMean_pos_iff.mpr
      simpa only [he, Nat.cast_zero] using hpos
    exact ((not_lt_of_ge hbad) hpos').elim
  · exact he

theorem IsMaximumIndependentOn.mem_of_rootDefect_one
    {G : SimpleGraph V} {S I : Finset V} {v : V} (hI : IsMaximumIndependentOn G S I)
    (hd : rootDefect G S v = 1) : v ∈ I := by
  by_contra hn
  have hi : I ∈ independentSubsets G (S.erase v) := by
    refine mem_independentSubsets.mpr ⟨?_, hI.independent⟩
    intro x hx
    exact mem_erase.mpr ⟨fun he => hn (he ▸ hx), hI.subset hx⟩
  have hc : I.card ≤ independenceNumberOn G (S.erase v) := Finset.le_sup hi
  rw [hI.card_eq_independenceNumberOn] at hc
  unfold rootDefect at hd
  omega

theorem IsRootedBlockAttachment.whole_rootDefect_eq_one
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w)
    (hH : rootDefect G H v = 1) (hT : independenceNumberOn G T = independenceNumberOn G (T.erase w)) :
    rootDefect G (H ∪ T) v = 1 := by
  have hvT : v ∉ T := fun hv => disjoint_left.mp h.disjoint h.host_root_mem hv
  have herase : (H ∪ T).erase v = H.erase v ∪ T := by
    ext x
    by_cases hx : x = v <;> simp [hx, hvT]
  have hcross : ∀ x ∈ H.erase v, ∀ y ∈ T, ¬ G.Adj x y := by
    intro x hx y hy hadj
    exact (mem_erase.mp hx).1 ((h.cross x (mem_of_mem_erase hx) y hy).mp hadj).1
  have he := independenceNumberOn_disjoint_union G (H.erase v) T
    (h.disjoint.mono (erase_subset _ _) (Subset.refl _)) hcross
  have hf := h.independenceNumber_add_defects
  have hdT : rootDefect G T w = 0 := by simp [rootDefect, hT]
  rw [hdT, mul_zero, add_zero] at hf
  unfold rootDefect at hH ⊢
  rw [herase, he, hf]
  omega

theorem IsRootedBlockAttachment.host_root_mem_every_maximum_of_terminal_nonpos
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w) (hG : G.IsAcyclic)
    (hsmaller : GlobalSmallerMeanHyp.{u} (H ∪ T).card)
    {i : Fin 8} (hp : InducedIso.BranchParameters G T w i) (hi : i = 0 ∨ i = 1)
    (hbad : adjustedMeanPotential G (H ∪ T) (independenceNumberOn G (H ∪ T)) ≤ 0)
    {I : Finset V} (hI : IsMaximumIndependentOn G (H ∪ T) I) : v ∈ I :=
  hI.mem_of_rootDefect_one (h.whole_rootDefect_eq_one
    (h.host_rootDefect_eq_one_of_terminal_nonpos hG hsmaller hp hi hbad) hp.root_state_zero)

theorem PendantPathExtension.erase_endpoints_alpha_of_even
    {G : SimpleGraph V} {T : Finset V} {tip root : V} {n : ℕ}
    (h : PendantPathExtension G {tip} tip n T root) (hn : n % 2 = 0) :
    independenceNumberOn G ((T.erase root).erase tip) =
      independenceNumberOn G (T.erase root) := by
  cases h with
  | zero _ => simp
  | @succ n B w h root hroot hadj =>
    rw [erase_insert hroot]
    have ht := h.initial_delete_alpha
    have hc := congrArg Prod.fst h.card_transfer
    rw [independenceNumberOn_singleton] at hc
    have he : independenceNumberOn G ∅ = 0 := by
      simp [independenceNumberOn, independentSubsets_empty_eq_singleton]
    simp only [erase_singleton, he, pathCardTransfer_from_singleton] at hc
    rw [ht, hc]
    omega

/-- A maximum set containing the attachment vertex can be exchanged to
omit the far tip of an odd-order path branch. -/
theorem IsRootedBlockAttachment.exists_maximum_omitting_odd_path_tip
    {G : SimpleGraph V} {H T I : Finset V} {v root tip : V} {n : ℕ}
    (h : IsRootedBlockAttachment G H v T root)
    (hpath : PendantPathExtension G {tip} tip n T root) (hn : n % 2 = 0)
    (hI : IsMaximumIndependentOn G (H ∪ T) I) (hvI : v ∈ I) :
    ∃ J : Finset V, IsMaximumIndependentOn G (H ∪ T) J ∧ tip ∉ J := by
  have htip : tip ∈ T := hpath.host_subset (mem_singleton_self _)
  have hvr : G.Adj v root :=
    (h.cross v h.host_root_mem root h.block_root_mem).mpr ⟨rfl, rfl⟩
  have hrI : root ∉ I := fun hr => hI.independent hvI hr (G.ne_of_adj hvr) hvr
  have hpart : I ∩ T ∈ independentSubsets G (T.erase root) := by
    apply mem_independentSubsets.mpr
    refine ⟨?_, hI.independent.mono (coe_subset.mpr inter_subset_left)⟩
    intro x hx
    exact mem_erase.mpr ⟨fun he => hrI (he ▸ (mem_inter.mp hx).1), (mem_inter.mp hx).2⟩
  have hib : (I ∩ T).card ≤ independenceNumberOn G (T.erase root) := Finset.le_sup hpart
  obtain ⟨K, hK⟩ := exists_maximumIndependentOn G ((T.erase root).erase tip)
  have hkcard : independenceNumberOn G (T.erase root) = K.card :=
    (hpath.erase_endpoints_alpha_of_even hn).symm.trans hK.card_eq_independenceNumberOn.symm
  have hcross : ∀ x ∈ H, ∀ y ∈ (T.erase root).erase tip, ¬G.Adj x y := by
    intro x hx y hy hxy
    exact (mem_erase.mp (mem_of_mem_erase hy)).1 ((h.cross x hx y
      (mem_of_mem_erase (mem_of_mem_erase hy))).mp hxy).2
  have hmem := independentSubsets_union_of_no_cross_edges hcross
    (independentSubsets_inter_left hI.1) hK.1
  have hKS : (T.erase root).erase tip ⊆ T := (erase_subset _ _).trans (erase_subset _ _)
  have hmem' : (I ∩ H) ∪ K ∈ independentSubsets G (H ∪ T) :=
    independentSubsets_mono G (union_subset_union (Subset.refl _) hKS) hmem
  have hsplit := union_inter_split hI.subset
  have hdis := h.disjoint.mono
    (show I ∩ H ⊆ H from inter_subset_right) (show I ∩ T ⊆ T from inter_subset_right)
  have hdisK := h.disjoint.mono
    (show I ∩ H ⊆ H from inter_subset_right) (hK.subset.trans hKS)
  have hcount : I.card = (I ∩ H).card + (I ∩ T).card := by
    calc
      I.card = ((I ∩ H) ∪ (I ∩ T)).card := congrArg Finset.card hsplit.symm
      _ = _ := card_union_of_disjoint hdis
  have hnew : I.card ≤ ((I ∩ H) ∪ K).card := by
    rw [card_union_of_disjoint hdisK, ← hkcard]
    omega
  refine ⟨(I ∩ H) ∪ K, ⟨hmem', fun J hJ => (hI.2 J hJ).trans hnew⟩, ?_⟩
  intro ht
  rcases mem_union.mp ht with ht | ht
  · exact disjoint_left.mp h.disjoint (mem_inter.mp ht).2 htip
  · exact (mem_erase.mp (hK.subset ht)).1 rfl

/-- A genuine nonempty extension ends at an actual leaf, including when
the initial host has arbitrary internal structure. -/
theorem PendantPathExtension.endpoint_leaf {G : SimpleGraph V} {H S : Finset V}
    {v tip : V} {n : ℕ} (h : PendantPathExtension G H v n S tip) (hn : 0 < n) :
    ∃ a ∈ S, G.Adj tip a ∧ ∀ x ∈ S, G.Adj tip x → x = a := by
  cases h with
  | zero _ => omega
  | @succ n B root hp tip ht hadj =>
    refine ⟨root, mem_insert_of_mem hp.endpoint_mem,
      (hadj root hp.endpoint_mem).mpr rfl, ?_⟩
    intro x hx htx
    rcases mem_insert.mp hx with rfl | hx
    · exact (G.irrefl htx).elim
    · exact (hadj x hx).mp htx

theorem IsRootedBlockAttachment.path_tip_is_leaf
    {G : SimpleGraph V} {H T : Finset V} {v root tip : V} {n : ℕ}
    (h : IsRootedBlockAttachment G H v T root)
    (hp : PendantPathExtension G {tip} tip n T root) :
    ∃ a ∈ H ∪ T, G.Adj tip a ∧ ∀ x ∈ H ∪ T, G.Adj tip x → x = a := by
  apply (hp.reverse_attach H v h.host_root_mem h.disjoint ?_).endpoint_leaf (by omega)
  intro x hx y hy
  simpa only [G.adj_comm, and_comm] using h.cross y hy x hx

/-- If both the host root and the path tip occur in every maximum set,
the actual attached path has even order. -/
theorem IsRootedBlockAttachment.path_order_even_of_forced_endpoints
    {G : SimpleGraph V} {H T : Finset V} {v root tip : V} {n : ℕ}
    (h : IsRootedBlockAttachment G H v T root)
    (hp : PendantPathExtension G {tip} tip n T root)
    (hv : ∀ I, IsMaximumIndependentOn G (H ∪ T) I → v ∈ I)
    (ht : ∀ I, IsMaximumIndependentOn G (H ∪ T) I → tip ∈ I) :
    (n + 1) % 2 = 0 := by
  by_contra hn
  obtain ⟨I, hI⟩ := exists_maximumIndependentOn G (H ∪ T)
  obtain ⟨J, hJ, htJ⟩ := h.exists_maximum_omitting_odd_path_tip hp (by omega) hI (hv I hI)
  exact htJ (ht J hJ)

/-- In a minimal nonpositive forest every ordinary path attached at a
forced vertex has even order; the far-tip condition follows from actual
leaf deletion, rather than being supplied as a graph-message premise. -/
theorem IsRootedBlockAttachment.path_order_even_of_nonpos
    {G : SimpleGraph V} {H T : Finset V} {v root tip : V} {n : ℕ}
    (h : IsRootedBlockAttachment G H v T root)
    (hp : PendantPathExtension G {tip} tip n T root) (hG : G.IsAcyclic)
    (hsmaller : GlobalSmallerMeanHyp.{u} (H ∪ T).card)
    (hbad : adjustedMeanPotential G (H ∪ T) (independenceNumberOn G (H ∪ T)) ≤ 0)
    (hv : ∀ I, IsMaximumIndependentOn G (H ∪ T) I → v ∈ I) :
    (n + 1) % 2 = 0 := by
  apply h.path_order_even_of_forced_endpoints hp hv
  intro I hI
  obtain ⟨a, _, _, hleaf⟩ := h.path_tip_is_leaf hp
  apply hI.leaf_mem_of_adjustedMean_nonpos
    (by rwa [hI.card_eq_independenceNumberOn])
    (hsmaller.same_graph G hG (H ∪ T) rfl)
    (mem_union_right H (hp.host_subset (mem_singleton_self _))) hleaf

#print axioms InducedIso.BranchParameters.E_zero_pos
#print axioms IsRootedBlockAttachment.host_rootDefect_eq_one_of_terminal_nonpos
#print axioms IsRootedBlockAttachment.host_root_mem_every_maximum_of_terminal_nonpos
#print axioms IsRootedBlockAttachment.exists_maximum_omitting_odd_path_tip
#print axioms IsRootedBlockAttachment.path_order_even_of_forced_endpoints
#print axioms IsRootedBlockAttachment.path_order_even_of_nonpos
end ForestUnimodality
