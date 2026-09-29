import ForestUnimodality.TreeTerminalDecomposition

/-! Exact distance control for the penultimate branching level of a tree. -/
namespace ForestUnimodality
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [DecidableEq V] in
theorem dist_add_of_mem_path {G : SimpleGraph V} (hG : G.IsAcyclic)
    {r v c : V} {p : G.Walk r v} (hp : p.IsPath) (hc : c ∈ p.support) :
    G.dist r v = G.dist r c + G.dist c v := by
  obtain ⟨p₁, p₂, hp₁, hp₂, heq⟩ := hp.mem_support_iff_exists_append.mp hc
  have hlen := path_length_eq_dist_of_isAcyclic hG hp
  rw [heq, Walk.length_append, path_length_eq_dist_of_isAcyclic hG hp₁,
    path_length_eq_dist_of_isAcyclic hG hp₂] at hlen
  exact hlen.symm

theorem dist_add_of_other_deletedCenterBranch (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) {c r v : V} (hconn : (G.induce (S : Set V)).Connected)
    (hr : r ∈ S.erase c)
    (i : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent)
    (hi : i ≠ (G.induce ((S.erase c : Finset V) : Set V)).connectedComponentMk ⟨r, hr⟩)
    (hv : v ∈ deletedCenterBranch G S c i) :
    G.dist r v = G.dist r c + G.dist c v := by
  classical
  have hv' := deletedCenterBranch_subset G S c i hv
  let f : G.induce (S : Set V) →g G := ⟨Subtype.val, fun h => h⟩
  obtain ⟨p, hp⟩ := (hconn.preconnected ⟨r, mem_of_mem_erase hr⟩
    ⟨v, mem_of_mem_erase hv'⟩).exists_isPath
  let q := p.map f
  have hq : q.IsPath := hp.map Subtype.val_injective
  have hcq : c ∈ q.support := by
    by_contra hcq
    have hsub : ∀ x ∈ q.support, x ∈ (S.erase c : Set V) := by
      intro x hx
      obtain ⟨y, _, hy⟩ := List.mem_map.mp
        (show x ∈ p.support.map f by simpa only [q, Walk.support_map] using hx)
      exact mem_erase.mpr ⟨fun he => hcq (he ▸ hx), hy ▸ y.2⟩
    have he := ConnectedComponent.eq.mpr (q.induce (S.erase c : Set V) hsub).reachable
    obtain ⟨hv'', hvi⟩ := (mem_deletedCenterBranch G S c i v).mp hv
    exact hi (hvi.symm.trans he.symm)
  exact dist_add_of_mem_path hG hq hcq

theorem branching_adj_of_depth_bound (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) {c r : V} (hconn : (G.induce (S : Set V)).Connected)
    (hr : r ∈ S.erase c)
    (hbound : ∀ x ∈ S, 3 ≤ degreeOn G S x → G.dist r x ≤ G.dist r c + 1)
    (i : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent)
    (hi : i ≠ (G.induce ((S.erase c : Finset V) : Set V)).connectedComponentMk ⟨r, hr⟩)
    {x : V} (hx : x ∈ deletedCenterBranch G S c i) (hxd : 3 ≤ degreeOn G S x) :
    G.Adj c x := by
  have hxS := mem_of_mem_erase (deletedCenterBranch_subset G S c i hx)
  have hadd := dist_add_of_other_deletedCenterBranch G hG S hconn hr i hi hx
  have hlt := dist_lt_of_other_deletedCenterBranch G hG S hconn hr i hi hx
  have hle := hbound x hxS hxd
  apply dist_eq_one_iff_adj.mp
  omega

theorem unique_branching_of_depth_bound (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) {c r : V} (hconn : (G.induce (S : Set V)).Connected)
    (hr : r ∈ S.erase c)
    (hbound : ∀ x ∈ S, 3 ≤ degreeOn G S x → G.dist r x ≤ G.dist r c + 1)
    (i : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent)
    (hi : i ≠ (G.induce ((S.erase c : Finset V) : Set V)).connectedComponentMk ⟨r, hr⟩)
    {x y : V} (hx : x ∈ deletedCenterBranch G S c i) (hy : y ∈ deletedCenterBranch G S c i)
    (hxd : 3 ≤ degreeOn G S x) (hyd : 3 ≤ degreeOn G S y) : x = y := by
  have hn : c ∉ deletedCenterBranch G S c i := fun hc =>
    (mem_erase.mp (deletedCenterBranch_subset G S c i hc)).1 rfl
  exact unique_adj_to_connected_region G hG _ hn (deletedCenterBranch_connected G S c i) hx hy
    (branching_adj_of_depth_bound G hG S hconn hr hbound i hi hx hxd)
    (branching_adj_of_depth_bound G hG S hconn hr hbound i hi hy hyd)

omit [DecidableEq V] in
theorem IsRootedBlockAttachment.dist_block_root {G : SimpleGraph V}
    (hG : G.IsAcyclic) {H T : Finset V} {p c r : V}
    (h : IsRootedBlockAttachment G H p T c)
    (hconn : (G.induce (H : Set V)).Connected) (hr : r ∈ H) :
    G.dist r c = G.dist r p + 1 := by
  let f : G.induce (H : Set V) →g G := ⟨Subtype.val, fun h => h⟩
  obtain ⟨q, hq⟩ := (hconn.preconnected ⟨r, hr⟩ ⟨p, h.host_root_mem⟩).exists_isPath
  have hq' : (q.map f).IsPath := hq.map Subtype.val_injective
  have hnot : c ∉ (q.map f).support := by
    rw [Walk.support_map]
    intro hc
    obtain ⟨x, _, hx⟩ := List.mem_map.mp hc
    exact h.block_root_not_host (hx ▸ x.2)
  have hadj := (h.cross p h.host_root_mem c h.block_root_mem).mpr ⟨rfl, rfl⟩
  have he := path_length_eq_dist_of_isAcyclic hG (hq'.concat hnot hadj)
  rw [Walk.length_concat, path_length_eq_dist_of_isAcyclic hG hq'] at he
  exact he.symm

/-- A farthest actual branching center can be chosen with its connected
upstream host and its global depth bound retained in the witness. -/
theorem exists_farthest_terminal_spider (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (hconn : (G.induce (S : Set V)).Connected)
    {r d : V} (hr : r ∈ S) (hd : d ∈ S) (hdr : d ≠ r)
    (hdd : 3 ≤ degreeOn G S d) :
    ∃ c, ∃ _hc : c ∈ S, ∃ hcr : c ≠ r,
    let ι := (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent
    let i₀ := (G.induce ((S.erase c : Finset V) : Set V)).connectedComponentMk
      ⟨r, mem_erase.mpr ⟨hcr.symm, hr⟩⟩
    ∃ (H T : Finset V) (p : V) (root tip : ι → V) (length : ι → ℕ),
      IsTerminalSpiderOn G S c H T p (univ.erase i₀)
        (deletedCenterBranch G S c) root tip length ∧
      r ∈ H ∧ (G.induce (H : Set V)).Connected ∧
      ∀ x ∈ S, 3 ≤ degreeOn G S x → G.dist r x ≤ G.dist r c := by
  classical
  let M := S.filter fun x => 3 ≤ degreeOn G S x
  obtain ⟨c, hcM, hmax⟩ := M.exists_max_image (G.dist r) ⟨d, mem_filter.mpr ⟨hd, hdd⟩⟩
  have hc := (mem_filter.mp hcM).1
  have hcd := (mem_filter.mp hcM).2
  have hcr : c ≠ r := by
    intro he
    have hle := hmax d (mem_filter.mpr ⟨hd, hdd⟩)
    rw [he, dist_self] at hle
    let f : G.induce (S : Set V) →g G := ⟨Subtype.val, fun h => h⟩
    have hp := ((hconn.preconnected ⟨r, hr⟩ ⟨d, hd⟩).map f).pos_dist_of_ne hdr.symm
    change 0 < G.dist r d at hp
    omega
  have hr' : r ∈ S.erase c := mem_erase.mpr ⟨hcr.symm, hr⟩
  have hdeg : ∀ (i : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent),
      i ≠ (G.induce ((S.erase c : Finset V) : Set V)).connectedComponentMk ⟨r, hr'⟩ →
      ∀ x ∈ deletedCenterBranch G S c i, degreeOn G S x ≤ 2 := by
    intro i hi x hx
    by_contra! hn
    have hxS := mem_of_mem_erase (deletedCenterBranch_subset G S c i hx)
    have hle := hmax x (mem_filter.mpr ⟨hxS, by omega⟩)
    have hlt := dist_lt_of_other_deletedCenterBranch G hG S hconn hr' i hi hx
    omega
  obtain ⟨H, T, p, root, tip, len, ht, hH⟩ :=
    terminal_spider_of_no_branch_away_with_host G hG S hc hr' hconn hcd hdeg
  refine ⟨c, hc, hcr, H, T, p, root, tip, len, ht, ?_, ?_, ?_⟩
  · rw [hH]
    exact (mem_deletedCenterBranch G S c _ r).mpr ⟨hr', rfl⟩
  · rw [hH]
    exact deletedCenterBranch_connected G S c _
  · intro x hx hxd
    exact hmax x (mem_filter.mpr ⟨hx, hxd⟩)

#print axioms dist_add_of_other_deletedCenterBranch
#print axioms branching_adj_of_depth_bound
#print axioms unique_branching_of_depth_bound
#print axioms IsRootedBlockAttachment.dist_block_root
#print axioms exists_farthest_terminal_spider
end ForestUnimodality
