import ForestUnimodality.TerminalBridgePruning

/-! Actual finite branches simultaneously attached to a retained host root.
The partition, moment, and independence identities are graph statements. -/

namespace ForestUnimodality
open Finset
universe u v
variable {V : Type u} {ι : Type v} [DecidableEq V] [DecidableEq ι]

structure IsRootedFanAttachment (G : SimpleGraph V) (S K : Finset V) (u : V)
    (s : Finset ι) (B : ι → Finset V) (root : ι → V) : Prop where
  vertices : S = K ∪ s.biUnion B
  host_root_mem : u ∈ K
  separated : IsSeparatedFamily G s B
  attachments : ∀ i ∈ s, IsRootedBlockAttachment G K u (B i) (root i)

namespace IsRootedFanAttachment

variable {G : SimpleGraph V} {S K : Finset V} {u : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanAttachment G S K u s B root)

include h

omit [DecidableEq ι] in
theorem disjoint : Disjoint K (s.biUnion B) := by
  apply disjoint_left.mpr
  intro x hxK hxU
  obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hxU
  exact disjoint_left.mp (h.attachments i hi).disjoint hxK hxi

omit [DecidableEq ι] in
theorem root_not_union : u ∉ s.biUnion B :=
  fun hu => disjoint_left.mp h.disjoint h.host_root_mem hu

omit [DecidableEq ι] in
theorem root_mem : u ∈ S := by
  rw [h.vertices]
  exact mem_union_left _ h.host_root_mem

omit [DecidableEq ι] h in
theorem deleted_subset (s : Finset ι) (B : ι → Finset V) (root : ι → V) :
    s.biUnion (fun i => (B i).erase (root i)) ⊆ s.biUnion B := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx
  exact mem_biUnion.mpr ⟨i, hi, mem_of_mem_erase hxi⟩

omit [DecidableEq ι] in
theorem no_edges_erase_host :
    ∀ x ∈ K.erase u, ∀ y ∈ s.biUnion B, ¬ G.Adj x y := by
  intro x hx y hy hxy
  obtain ⟨i, hi, hyi⟩ := mem_biUnion.mp hy
  exact (mem_erase.mp hx).1
    (((h.attachments i hi).cross x (mem_of_mem_erase hx) y hyi).mp hxy).1

omit [DecidableEq ι] in
theorem no_edges_deleted_branches :
    ∀ x ∈ K, ∀ y ∈ s.biUnion (fun i => (B i).erase (root i)), ¬ G.Adj x y := by
  intro x hx y hy hxy
  obtain ⟨i, hi, hyi⟩ := mem_biUnion.mp hy
  exact (mem_erase.mp hyi).1
    (((h.attachments i hi).cross x hx y (mem_of_mem_erase hyi)).mp hxy).2

omit [DecidableEq ι] in
theorem erase_root : S.erase u = K.erase u ∪ s.biUnion B := by
  rw [h.vertices]
  ext x
  simp only [mem_erase, mem_union]
  constructor
  · rintro ⟨hxu, hxK | hxU⟩
    · exact Or.inl ⟨hxu, hxK⟩
    · exact Or.inr hxU
  · rintro (⟨hxu, hxK⟩ | hxU)
    · exact ⟨hxu, Or.inl hxK⟩
    · exact ⟨fun he => h.root_not_union (he ▸ hxU), Or.inr hxU⟩

omit [DecidableEq ι] in
theorem delete_closed_root : S \ closedNeighborhoodIn G S u =
    (K \ closedNeighborhoodIn G K u) ∪ s.biUnion (fun i => (B i).erase (root i)) := by
  ext x
  rw [mem_sdiff_closedNeighborhoodIn, h.vertices]
  simp only [mem_union, mem_biUnion, mem_erase, mem_sdiff_closedNeighborhoodIn]
  constructor
  · rintro ⟨hxK | ⟨i, hi, hxi⟩, hxu, hno⟩
    · exact Or.inl ⟨hxK, hxu, hno⟩
    · refine Or.inr ⟨i, hi, ?_, hxi⟩
      intro he
      exact hno (((h.attachments i hi).cross u h.host_root_mem x hxi).mpr ⟨rfl, he⟩)
  · rintro (⟨hxK, hxu, hno⟩ | ⟨i, hi, hxr, hxi⟩)
    · exact ⟨Or.inl hxK, hxu, hno⟩
    · refine ⟨Or.inr ⟨i, hi, hxi⟩, ?_, ?_⟩
      · intro he
        exact (h.attachments i hi).host_root_not_block (he ▸ hxi)
      · intro hux
        exact hxr (((h.attachments i hi).cross u h.host_root_mem x hxi).mp hux).2

omit [DecidableEq ι] in
theorem partitionFunction_eq (z : ℝ) :
    partitionFunction G S z =
      partitionFunction G (s.biUnion (fun i => (B i).erase (root i))) z * partitionFunction G K z +
      (partitionFunction G (s.biUnion B) z -
        partitionFunction G (s.biUnion (fun i => (B i).erase (root i))) z) *
        partitionFunction G (K.erase u) z := by
  have hF := partitionFunction_delete_vertex G S h.root_mem z
  have hK := partitionFunction_delete_vertex G K h.host_root_mem z
  rw [h.erase_root, h.delete_closed_root,
    partitionFunction_disjoint_union G (K.erase u) (s.biUnion B)
      (h.disjoint.mono (erase_subset _ _) (Subset.refl _)) h.no_edges_erase_host,
    partitionFunction_disjoint_union G (K \ closedNeighborhoodIn G K u)
      (s.biUnion (fun i => (B i).erase (root i)))
      (h.disjoint.mono sdiff_subset (deleted_subset s B root))
      (fun x hx => h.no_edges_deleted_branches x (mem_sdiff.mp hx).1)] at hF
  rw [hF, hK]
  ring

omit [DecidableEq ι] in
theorem firstMoment_eq (z : ℝ) :
    hardCoreMomentNumerator G S 1 z =
      partitionFunction G (s.biUnion (fun i => (B i).erase (root i))) z *
        hardCoreMomentNumerator G K 1 z +
      (partitionFunction G (s.biUnion B) z -
        partitionFunction G (s.biUnion (fun i => (B i).erase (root i))) z) *
        hardCoreMomentNumerator G (K.erase u) 1 z +
      hardCoreMomentNumerator G (s.biUnion (fun i => (B i).erase (root i))) 1 z *
        partitionFunction G K z +
      (hardCoreMomentNumerator G (s.biUnion B) 1 z -
        hardCoreMomentNumerator G (s.biUnion (fun i => (B i).erase (root i))) 1 z) *
        partitionFunction G (K.erase u) z := by
  have hF := hardCore_first_moment_delete_vertex G S h.root_mem z
  have hK := hardCore_first_moment_delete_vertex G K h.host_root_mem z
  have hZK := partitionFunction_delete_vertex G K h.host_root_mem z
  rw [h.erase_root, h.delete_closed_root,
    hardCore_first_moment_disjoint_union G (K.erase u) (s.biUnion B)
      (h.disjoint.mono (erase_subset _ _) (Subset.refl _)) h.no_edges_erase_host,
    hardCore_first_moment_disjoint_union G (K \ closedNeighborhoodIn G K u)
      (s.biUnion (fun i => (B i).erase (root i)))
      (h.disjoint.mono sdiff_subset (deleted_subset s B root))
      (fun x hx => h.no_edges_deleted_branches x (mem_sdiff.mp hx).1),
    partitionFunction_disjoint_union G (K \ closedNeighborhoodIn G K u)
      (s.biUnion (fun i => (B i).erase (root i)))
      (h.disjoint.mono sdiff_subset (deleted_subset s B root))
      (fun x hx => h.no_edges_deleted_branches x (mem_sdiff.mp hx).1)] at hF
  rw [hF, hK, hZK]
  ring

theorem independenceNumber_eq
    (hzero : ∀ i ∈ s, independenceNumberOn G (B i) = independenceNumberOn G ((B i).erase (root i))) :
    independenceNumberOn G S = independenceNumberOn G K + independenceNumberOn G (s.biUnion B) := by
  have hsum : independenceNumberOn G (s.biUnion (fun i => (B i).erase (root i))) =
      independenceNumberOn G (s.biUnion B) := by
    rw [(h.separated.subsets (fun _ _ => erase_subset _ _)).independenceNumber_biUnion,
      h.separated.independenceNumber_biUnion]
    exact sum_congr rfl (fun i hi => (hzero i hi).symm)
  apply le_antisymm
  · apply Finset.sup_le
    intro L hL
    rw [h.vertices] at hL
    have ha : (L ∩ K).card ≤ independenceNumberOn G K :=
      Finset.le_sup (independentSubsets_inter_left hL)
    have hb : (L ∩ s.biUnion B).card ≤ independenceNumberOn G (s.biUnion B) :=
      Finset.le_sup (independentSubsets_inter_right hL)
    have hsplit := union_inter_split (mem_independentSubsets.mp hL).1
    have hc := card_union_of_disjoint (h.disjoint.mono
      (show L ∩ K ⊆ K from inter_subset_right)
      (show L ∩ s.biUnion B ⊆ s.biUnion B from inter_subset_right))
    rw [hsplit] at hc
    omega
  · have he := independenceNumberOn_disjoint_union G K
      (s.biUnion (fun i => (B i).erase (root i)))
      (h.disjoint.mono (Subset.refl _) (deleted_subset s B root)) h.no_edges_deleted_branches
    rw [hsum] at he
    rw [← he]
    apply independenceNumberOn_mono
    rw [h.vertices]
    exact union_subset_union (Subset.refl _) (deleted_subset s B root)

omit [DecidableEq ι] in
theorem card : S.card = K.card + (s.biUnion B).card := by
  rw [h.vertices, card_union_of_disjoint h.disjoint]

/-- Exact potential identity in the same variables consumed by the scalar
fan certificate. All union statistics still refer to actual graphs. -/
theorem adjustedMean_identity
    (hzero : ∀ i ∈ s, independenceNumberOn G (B i) = independenceNumberOn G ((B i).erase (root i)))
    (hstate : rootDefect G K u = 1) :
    let U := s.biUnion B
    let D := s.biUnion (fun i => (B i).erase (root i))
    let A := partitionFunction G D (2 : ℝ)
    let P := partitionFunction G U (2 : ℝ)
    let r := partitionFunction G K (2 : ℝ) / partitionFunction G (K.erase u) 2
    let X := r * adjustedMeanPotential G K (independenceNumberOn G K)
    let Y := adjustedMeanPotential G (K.erase u) (independenceNumberOn G (K.erase u))
    let a := adjustedMeanPotential G U (independenceNumberOn G U)
    let b := 3 * hardCoreMean G D 2 - (independenceNumberOn G U : ℝ) - (29 / 60 : ℝ) * U.card
    60 * partitionFunction G S (2 : ℝ) * adjustedMeanPotential G S (independenceNumberOn G S) =
      partitionFunction G (K.erase u) 2 *
        (60 * A * (X + (P / A - 1) * Y + P / A * (a - 89 / 60) + (r - 1) * b + 89 / 60)) := by
  dsimp only
  have hZ := h.partitionFunction_eq (2 : ℝ)
  have hM := h.firstMoment_eq (2 : ℝ)
  have ha := h.independenceNumber_eq hzero
  have hn := h.card
  have hna : K.card = (K.erase u).card + 1 := (card_erase_add_one h.host_root_mem).symm
  have haa : independenceNumberOn G K = independenceNumberOn G (K.erase u) + 1 := by
    have hb := (independenceNumberOn_erase_bounds G K u).1
    unfold rootDefect at hstate
    omega
  have hZS := ne_of_gt (partitionFunction_pos G S (by norm_num : (0 : ℝ) ≤ 2))
  have hZK := ne_of_gt (partitionFunction_pos G K (by norm_num : (0 : ℝ) ≤ 2))
  have hZJ := ne_of_gt (partitionFunction_pos G (K.erase u) (by norm_num : (0 : ℝ) ≤ 2))
  have hZU := ne_of_gt (partitionFunction_pos G (s.biUnion B) (by norm_num : (0 : ℝ) ≤ 2))
  have hZD := ne_of_gt (partitionFunction_pos G (s.biUnion (fun i => (B i).erase (root i)))
    (by norm_num : (0 : ℝ) ≤ 2))
  unfold adjustedMeanPotential hardCoreMean
  rw [ha, hn, haa, hna]
  push_cast
  field_simp
  rw [hM, hZ]
  ring

end IsRootedFanAttachment

#print axioms IsRootedFanAttachment.partitionFunction_eq
#print axioms IsRootedFanAttachment.firstMoment_eq
#print axioms IsRootedFanAttachment.independenceNumber_eq
#print axioms IsRootedFanAttachment.adjustedMean_identity
end ForestUnimodality
