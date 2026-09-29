import ForestUnimodality.TreeSpiderDecomposition
import ForestUnimodality.RootedBlockAttachment

/-! Terminal branching vertices chosen by actual graph distance. -/
namespace ForestUnimodality
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [DecidableEq V] in
theorem path_length_eq_dist_of_isAcyclic {G : SimpleGraph V} (hG : G.IsAcyclic)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) : p.length = G.dist u v := by
  obtain ⟨q, hq, hlen⟩ := p.reachable.exists_path_of_dist
  have he := congrArg Subtype.val (hG.path_unique ⟨p, hp⟩ ⟨q, hq⟩)
  change p = q at he
  rwa [he]

theorem dist_lt_of_other_deletedCenterBranch (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) {c r v : V} (hconn : (G.induce (S : Set V)).Connected)
    (hr : r ∈ S.erase c)
    (i : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent)
    (hi : i ≠ (G.induce ((S.erase c : Finset V) : Set V)).connectedComponentMk ⟨r, hr⟩)
    (hv : v ∈ deletedCenterBranch G S c i) : G.dist r c < G.dist r v := by
  classical
  have hv' := deletedCenterBranch_subset G S c i hv
  let f : G.induce (S : Set V) →g G := ⟨Subtype.val, fun h => h⟩
  obtain ⟨p, hp⟩ := (hconn.preconnected ⟨r, mem_of_mem_erase hr⟩
    ⟨v, mem_of_mem_erase hv'⟩).exists_isPath
  let q := p.map f
  have hq : q.IsPath := hp.map Subtype.val_injective
  have hsub : ∀ x ∈ q.support, x ∈ S := by
    intro x hx
    obtain ⟨y, _, hy⟩ := List.mem_map.mp
      (show x ∈ p.support.map f by simpa only [q, Walk.support_map] using hx)
    exact hy ▸ y.2
  have hcq : c ∈ q.support := by
    by_contra hcq
    have hsub' : ∀ x ∈ q.support, x ∈ (S.erase c : Set V) := by
      intro x hx
      exact mem_erase.mpr ⟨fun he => hcq (he ▸ hx), hsub x hx⟩
    have hreach := (q.induce (S.erase c : Set V) hsub').reachable
    have he := ConnectedComponent.eq.mpr hreach
    obtain ⟨hv'', hvi⟩ := (mem_deletedCenterBranch G S c i v).mp hv
    exact hi (hvi.symm.trans he.symm)
  obtain ⟨q₁, q₂, hq₁, hq₂, heq⟩ := hq.mem_support_iff_exists_append.mp hcq
  have hlen := path_length_eq_dist_of_isAcyclic hG hq
  have hlen₁ := path_length_eq_dist_of_isAcyclic hG hq₁
  have hlen₂ := path_length_eq_dist_of_isAcyclic hG hq₂
  have hpos := q₂.reachable.pos_dist_of_ne (mem_erase.mp hv').1.symm
  rw [heq, Walk.length_append] at hlen
  change q₁.length + q₂.length = G.dist r v at hlen
  change q₁.length = G.dist r c at hlen₁
  change q₂.length = G.dist c v at hlen₂
  change 0 < G.dist c v at hpos
  omega

/-- Relative to any marked root and another marked vertex, there is a
distinct marked center whose every branch away from the root has degree
at most two in the original finite tree. -/
theorem exists_terminal_branching_center (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (hconn : (G.induce (S : Set V)).Connected)
    {r d : V} (hr : r ∈ S) (hd : d ∈ S) (hdr : d ≠ r)
    (hdd : 3 ≤ degreeOn G S d) :
    ∃ c, ∃ _hc : c ∈ S, ∃ hcr : c ≠ r, 3 ≤ degreeOn G S c ∧
      ∀ (i : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent),
      i ≠ (G.induce ((S.erase c : Finset V) : Set V)).connectedComponentMk
        ⟨r, mem_erase.mpr ⟨hcr.symm, hr⟩⟩ →
      ∀ x ∈ deletedCenterBranch G S c i, degreeOn G S x ≤ 2 := by
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
  refine ⟨c, hc, hcr, hcd, ?_⟩
  intro i hi x hx
  by_contra! hn
  have hxS := mem_of_mem_erase (deletedCenterBranch_subset G S c i hx)
  have hxM : x ∈ M := mem_filter.mpr ⟨hxS, by omega⟩
  have hle := hmax x hxM
  have hlt := dist_lt_of_other_deletedCenterBranch G hG S hconn
    (mem_erase.mpr ⟨hcr.symm, hr⟩) i hi hx
  omega

structure IsTerminalSpiderOn {ι : Type*} [DecidableEq ι] (G : SimpleGraph V)
    (S : Finset V) (c : V) (H T : Finset V) (p : V) (s : Finset ι)
    (B : ι → Finset V) (root tip : ι → V) (length : ι → ℕ) : Prop where
  vertices : S = H ∪ T
  attachment : IsRootedBlockAttachment G H p T c
  spider : IsSpiderOn G T c s B root tip length
  branches : 2 ≤ s.card

theorem terminal_spider_of_no_branch_away_with_host (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) {c r : V} (hc : c ∈ S) (hr : r ∈ S.erase c)
    (hconn : (G.induce (S : Set V)).Connected) (hcdeg : 3 ≤ degreeOn G S c)
    (hdeg : ∀ (i : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent),
      i ≠ (G.induce ((S.erase c : Finset V) : Set V)).connectedComponentMk ⟨r, hr⟩ →
      ∀ x ∈ deletedCenterBranch G S c i, degreeOn G S x ≤ 2) :
    let ι := (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent
    let i₀ := (G.induce ((S.erase c : Finset V) : Set V)).connectedComponentMk ⟨r, hr⟩
    ∃ (H T : Finset V) (p : V) (root tip : ι → V) (length : ι → ℕ),
      IsTerminalSpiderOn G S c H T p (univ.erase i₀)
        (deletedCenterBranch G S c) root tip length ∧ H = deletedCenterBranch G S c i₀ := by
  classical
  dsimp only
  let ι := (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent
  let i₀ : ι := (G.induce ((S.erase c : Finset V) : Set V)).connectedComponentMk ⟨r, hr⟩
  let B := deletedCenterBranch G S c
  let s : Finset ι := univ.erase i₀
  have hsep := deletedCenterBranch_separated G S c
  have hnot : ∀ i, c ∉ B i := fun i hi =>
    (mem_erase.mp (deletedCenterBranch_subset G S c i hi)).1 rfl
  have hroot : ∀ i, ∃ w ∈ B i, G.Adj c w := by
    intro i
    exact exists_adj_to_closed_region G S (B i) hc (hnot i)
      ((deletedCenterBranch_subset G S c i).trans (erase_subset _ _))
      (deletedCenterBranch_nonempty G S c i) hconn
      (fun x hx y hy hyc hxy => deletedCenterBranch_closed G S c i hx hy hyc hxy)
  choose root hrootmem hrootadj using hroot
  have hcenter : ∀ i, ∀ x ∈ B i, G.Adj c x ↔ x = root i := by
    intro i x hx
    exact ⟨fun hcx => unique_adj_to_connected_region G hG (B i) (hnot i)
      (deletedCenterBranch_connected G S c i) hx (hrootmem i) hcx (hrootadj i),
      fun he => he ▸ hrootadj i⟩
  have hpaths : ∀ i, ∃ u n, i ∈ s → PendantPathExtension G {u} u n (B i) (root i) := by
    intro i
    by_cases hi : i ∈ s
    · have hsub := deletedCenterBranch_subset G S c i
      have hd := hdeg i (mem_erase.mp hi).1
      have he := degreeOn_erase_of_adj G S hc (hrootadj i).symm
      have hdroot := hd (root i) (hrootmem i)
      have hrdeg : degreeOn G (B i) (root i) ≤ 1 := by
        have hm := degreeOn_mono G hsub (root i)
        change degreeOn G (deletedCenterBranch G S c i) (root i) ≤ 1
        omega
      obtain ⟨u, n, hp⟩ := exists_pendantPath_to_of_connected_degree_le_two G (B i)
        (hrootmem i) (deletedCenterBranch_connected G S c i)
        (fun x hx => (degreeOn_mono G (hsub.trans (erase_subset _ _)) x).trans (hd x hx)) hrdeg
      exact ⟨u, n, fun _ => hp⟩
    · exact ⟨c, 0, fun h => (hi h).elim⟩
  choose tip n hp using hpaths
  let H := B i₀
  let T := insert c (s.biUnion B)
  have hsp : IsSpiderOn G T c s B root tip (fun i => n i + 1) :=
    { vertices := rfl
      separated := hsep.mono (subset_univ _)
      root_mem := fun i _ => hrootmem i
      center_not_mem := fun i _ => hnot i
      center_adj := fun i _ => hcenter i
      length_pos := fun _ _ => Nat.zero_lt_succ _
      paths := fun i hi => by simpa using hp i hi }
  have hcover : H ∪ s.biUnion B = S.erase c := by
    have he : insert i₀ s = (univ : Finset ι) := insert_erase (mem_univ _)
    rw [← deletedCenterBranch_cover G S c, ← he, biUnion_insert]
  have hvertices : S = H ∪ T := by
    dsimp only [T]
    rw [union_insert, hcover, insert_erase hc]
  have hdis : Disjoint H T := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases mem_insert.mp hy with rfl | hy
    · exact hnot i₀ hx
    · obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hy
      exact Finset.disjoint_left.mp
        (hsep.disjoint i₀ (mem_univ _) i (mem_univ _) (mem_erase.mp hi).1.symm) hx hxi
  have hatt : IsRootedBlockAttachment G H (root i₀) T c := by
    refine ⟨hrootmem i₀, mem_insert_self _ _, hdis, ?_⟩
    intro x hx y hy
    rcases mem_insert.mp hy with hyc | hy
    · subst y
      exact ⟨fun hadj => ⟨(hcenter i₀ x hx).mp hadj.symm, rfl⟩,
        fun he => ((hcenter i₀ x hx).mpr he.1).symm⟩
    · obtain ⟨i, hi, hyi⟩ := mem_biUnion.mp hy
      have hn := hsep.no_edges i₀ (mem_univ _) i (mem_univ _)
        (mem_erase.mp hi).1.symm x hx y hyi
      exact ⟨fun he => (hn he).elim, fun he => (hnot i (he.2 ▸ hyi)).elim⟩
  have hinj : Function.Injective root := by
    intro i j he
    by_contra hij
    exact Finset.disjoint_left.mp (hsep.disjoint i (mem_univ _) j (mem_univ _) hij)
      (hrootmem i) (he ▸ hrootmem j)
  have hneigh : S.filter (G.Adj c) = (univ : Finset ι).image root := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxS, hcx⟩ := mem_filter.mp hx
      have hx' : x ∈ S.erase c := mem_erase.mpr ⟨hcx.ne.symm, hxS⟩
      rw [← deletedCenterBranch_cover G S c] at hx'
      obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hx'
      exact mem_image.mpr ⟨i, mem_univ _, ((hcenter i x hxi).mp hcx).symm⟩
    · rintro hx
      obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨mem_of_mem_erase (deletedCenterBranch_subset G S c i (hrootmem i)),
        hrootadj i⟩
  have hcard : degreeOn G S c = (univ : Finset ι).card := by
    rw [degreeOn_eq_card_filter, hneigh, card_image_of_injective _ hinj]
  have hs : 2 ≤ s.card := by
    have he : s.card + 1 = (univ : Finset ι).card := card_erase_add_one (mem_univ i₀)
    omega
  exact ⟨H, T, root i₀, root, tip, fun i => n i + 1, ⟨hvertices, hatt, hsp, hs⟩, rfl⟩

theorem terminal_spider_of_no_branch_away (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) {c r : V} (hc : c ∈ S) (hr : r ∈ S.erase c)
    (hconn : (G.induce (S : Set V)).Connected) (hcdeg : 3 ≤ degreeOn G S c)
    (hdeg : ∀ (i : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent),
      i ≠ (G.induce ((S.erase c : Finset V) : Set V)).connectedComponentMk ⟨r, hr⟩ →
      ∀ x ∈ deletedCenterBranch G S c i, degreeOn G S x ≤ 2) :
    let ι := (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent
    let i₀ := (G.induce ((S.erase c : Finset V) : Set V)).connectedComponentMk ⟨r, hr⟩
    ∃ (H T : Finset V) (p : V) (root tip : ι → V) (length : ι → ℕ),
      IsTerminalSpiderOn G S c H T p (univ.erase i₀)
        (deletedCenterBranch G S c) root tip length := by
  obtain ⟨H, T, p, root, tip, len, ht, _⟩ :=
    terminal_spider_of_no_branch_away_with_host G hG S hc hr hconn hcdeg hdeg
  exact ⟨H, T, p, root, tip, len, ht⟩

theorem exists_terminal_spider (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (hconn : (G.induce (S : Set V)).Connected)
    {r d : V} (hr : r ∈ S) (hd : d ∈ S) (hdr : d ≠ r)
    (hdd : 3 ≤ degreeOn G S d) :
    ∃ c, ∃ _hc : c ∈ S, ∃ hcr : c ≠ r,
    let ι := (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent
    let i₀ := (G.induce ((S.erase c : Finset V) : Set V)).connectedComponentMk
      ⟨r, mem_erase.mpr ⟨hcr.symm, hr⟩⟩
    ∃ (H T : Finset V) (p : V) (root tip : ι → V) (length : ι → ℕ),
      IsTerminalSpiderOn G S c H T p (univ.erase i₀)
        (deletedCenterBranch G S c) root tip length := by
  obtain ⟨c, hc, hcr, hcdeg, hdeg⟩ :=
    exists_terminal_branching_center G hG S hconn hr hd hdr hdd
  exact ⟨c, hc, hcr, terminal_spider_of_no_branch_away G hG S hc
    (mem_erase.mpr ⟨hcr.symm, hr⟩) hconn hcdeg hdeg⟩

#print axioms path_length_eq_dist_of_isAcyclic
#print axioms dist_lt_of_other_deletedCenterBranch
#print axioms exists_terminal_branching_center
#print axioms terminal_spider_of_no_branch_away
#print axioms exists_terminal_spider
end ForestUnimodality
