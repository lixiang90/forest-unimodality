import ForestUnimodality.TreeBranchDepth

/-! Actual center-component fans and their one-edge branch attachments. -/
namespace ForestUnimodality
open Finset SimpleGraph
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
attribute [local instance] Classical.propDecidable

omit [DecidableEq ι] in
theorem IsRootedFanOn.branch_subset {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) {i : ι} (hi : i ∈ s) : B i ⊆ S := by
  intro x hx
  rw [h.vertices]
  exact mem_insert_of_mem (mem_biUnion.mpr ⟨i, hi, hx⟩)

theorem IsRootedFanOn.degree_center {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) : degreeOn G S c = s.card := by
  classical
  have hinj : Set.InjOn root s := by
    intro i hi j hj he
    by_contra hij
    exact Finset.disjoint_left.mp (h.separated.disjoint i hi j hj hij)
      (h.root_mem i hi) (he ▸ h.root_mem j hj)
  have he : S.filter (G.Adj c) = s.image root := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxS, hcx⟩ := mem_filter.mp hx
      rw [h.vertices] at hxS
      rcases mem_insert.mp hxS with he | hxS
      · exact (hcx.ne he.symm).elim
      · obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hxS
        exact mem_image.mpr ⟨i, hi, ((h.center_adj i hi x hxi).mp hcx).symm⟩
    · intro hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨h.branch_subset hi (h.root_mem i hi),
        (h.center_adj i hi _ (h.root_mem i hi)).mpr rfl⟩
  rw [degreeOn_eq_card_filter, he, card_image_of_injOn hinj]

omit [DecidableEq ι] in
theorem IsRootedFanOn.branch_attachment {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) {i : ι} (hi : i ∈ s) :
    IsRootedBlockAttachment G (S \ B i) c (B i) (root i) := by
  refine ⟨mem_sdiff.mpr ⟨h.center_mem, h.center_not_mem i hi⟩, h.root_mem i hi,
    disjoint_sdiff_self_left, ?_⟩
  intro x hx y hy
  have hxS := (mem_sdiff.mp hx).1
  have hxB := (mem_sdiff.mp hx).2
  rw [h.vertices] at hxS
  rcases mem_insert.mp hxS with hxc | hxS
  · subst x
    simpa using h.center_adj i hi y hy
  · obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp hxS
    have hij : j ≠ i := fun he => hxB (he ▸ hxj)
    have hn := h.separated.no_edges j hj i hi hij x hxj y hy
    have hxc : x ≠ c := fun he => h.center_not_mem j hj (he ▸ hxj)
    simp only [hn, hxc, false_and]

omit [DecidableEq ι] in
theorem IsRootedFanOn.degree_branch_root {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) {i : ι} (hi : i ∈ s) :
    degreeOn G S (root i) = degreeOn G (B i) (root i) + 1 := by
  classical
  have hatt := h.branch_attachment hi
  have he : S.filter (G.Adj (root i)) = insert c ((B i).filter (G.Adj (root i))) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxS, hadj⟩ := mem_filter.mp hx
      by_cases hxi : x ∈ B i
      · exact mem_insert_of_mem (mem_filter.mpr ⟨hxi, hadj⟩)
      · have hxc := ((hatt.cross x (mem_sdiff.mpr ⟨hxS, hxi⟩)
          (root i) hatt.block_root_mem).mp hadj.symm).1
        exact mem_insert.mpr (Or.inl hxc)
    · intro hx
      rcases mem_insert.mp hx with rfl | hx
      · exact mem_filter.mpr ⟨h.center_mem,
          ((h.center_adj i hi _ (h.root_mem i hi)).mpr rfl).symm⟩
      · exact mem_filter.mpr ⟨h.branch_subset hi (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩
  have hn : c ∉ (B i).filter (G.Adj (root i)) := fun hc =>
    h.center_not_mem i hi (mem_filter.mp hc).1
  rw [degreeOn_eq_card_filter, he, card_insert_of_notMem hn, degreeOn_eq_card_filter]

theorem exists_component_rootedFan (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) {c : V} (hc : c ∈ S) (hconn : (G.induce (S : Set V)).Connected) :
    ∃ root : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent → V,
      IsRootedFanOn G S c univ (deletedCenterBranch G S c) root := by
  classical
  let B := deletedCenterBranch G S c
  have hnot : ∀ i, c ∉ B i := fun i hi =>
    (mem_erase.mp (deletedCenterBranch_subset G S c i hi)).1 rfl
  have hroot : ∀ i, ∃ w ∈ B i, G.Adj c w := by
    intro i
    exact exists_adj_to_closed_region G S (B i) hc (hnot i)
      ((deletedCenterBranch_subset G S c i).trans (erase_subset _ _))
      (deletedCenterBranch_nonempty G S c i) hconn
      (fun x hx y hy hyc hxy => deletedCenterBranch_closed G S c i hx hy hyc hxy)
  choose root hmem hadj using hroot
  refine ⟨root, ?_⟩
  refine { vertices := ?_
           separated := deletedCenterBranch_separated G S c
           root_mem := fun i _ => hmem i
           center_not_mem := fun i _ => hnot i
           center_adj := ?_ }
  · rw [deletedCenterBranch_cover, insert_erase hc]
  · intro i _ x hx
    exact ⟨fun hcx => unique_adj_to_connected_region G hG (B i) (hnot i)
      (deletedCenterBranch_connected G S c i) hx (hmem i) hcx (hadj i), fun he => he ▸ hadj i⟩

omit [DecidableEq ι] in
/-- A branch with a branching root and no further branching vertex is a
terminal spider of the whole graph, with the entire complement as host. -/
theorem IsRootedFanOn.exists_terminal_on_branch {G : SimpleGraph V} (hG : G.IsAcyclic)
    {S : Finset V} {c : V} {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) {i : ι} (hi : i ∈ s)
    (hconn : (G.induce (B i : Set V)).Connected) (hbranch : 3 ≤ degreeOn G S (root i))
    (hdeg : ∀ x ∈ B i, x ≠ root i → degreeOn G S x ≤ 2) :
    let κ := (G.induce (((B i).erase (root i) : Finset V) : Set V)).ConnectedComponent
    ∃ (rt tp : κ → V) (len : κ → ℕ),
      IsTerminalSpiderOn G S (root i) (S \ B i) (B i) c univ
        (deletedCenterBranch G (B i) (root i)) rt tp len := by
  classical
  obtain ⟨rt, tp, len, hsp⟩ := exists_spider_of_degree_le_two_off_center G hG (B i)
    (h.root_mem i hi) hconn
    (fun x hx hxr => (degreeOn_mono G (h.branch_subset hi) x).trans (hdeg x hx hxr))
  refine ⟨rt, tp, len, ⟨?_, h.branch_attachment hi, hsp, ?_⟩⟩
  · exact (sdiff_union_of_subset (h.branch_subset hi)).symm
  · have he := h.degree_branch_root hi
    have hf := hsp.toIsRootedFanOn.degree_center
    omega

#print axioms IsRootedFanOn.degree_center
#print axioms IsRootedFanOn.branch_attachment
#print axioms exists_component_rootedFan
#print axioms IsRootedFanOn.exists_terminal_on_branch
end ForestUnimodality
