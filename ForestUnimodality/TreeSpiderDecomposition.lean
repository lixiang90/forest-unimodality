import ForestUnimodality.TreePathDecomposition
import ForestUnimodality.ForestComponentPartition
import ForestUnimodality.SpiderMinimal

/-! Structural coverage: deleting the possible branching center of an
ordinary finite tree produces actual pendant paths. -/
namespace ForestUnimodality
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [DecidableEq V] in
theorem unique_adj_to_connected_region (G : SimpleGraph V) (hG : G.IsAcyclic)
    (B : Finset V) {c u v : V} (hc : c ∉ B)
    (hB : (G.induce (B : Set V)).Connected) (hu : u ∈ B) (hv : v ∈ B)
    (hcu : G.Adj c u) (hcv : G.Adj c v) : u = v := by
  classical
  let f : G.induce (B : Set V) →g G := ⟨Subtype.val, fun h => h⟩
  obtain ⟨p, hp⟩ := (hB.preconnected ⟨u, hu⟩ ⟨v, hv⟩).exists_isPath
  have hp' : (p.map f).IsPath := hp.map Subtype.val_injective
  have hnot : c ∉ (p.map f).support := by
    rw [Walk.support_map]
    intro hm
    obtain ⟨x, _, hx⟩ := List.mem_map.mp hm
    exact hc (hx ▸ x.2)
  have he := hG.eq_snd_of_adj_start (hp'.cons hnot (h := hcu)) hcv
    (Walk.end_mem_support (Walk.cons hcu (p.map f)))
  simpa [f] using he.symm

theorem exists_adj_to_closed_region (G : SimpleGraph V) (S B : Finset V)
    {c : V} (hc : c ∈ S) (hcB : c ∉ B) (hBS : B ⊆ S) (hne : B.Nonempty)
    (hconn : (G.induce (S : Set V)).Connected)
    (hclosed : ∀ x ∈ B, ∀ y ∈ S, y ≠ c → G.Adj x y → y ∈ B) :
    ∃ x ∈ B, G.Adj c x := by
  classical
  by_contra! hn
  have hstay : ∀ (x y : (S : Set V)), x.1 ∈ B →
      (G.induce (S : Set V)).Adj x y → y.1 ∈ B := by
    intro x y hx hxy
    by_cases hy : y.1 = c
    · exact (hn x.1 hx (hy ▸ hxy.symm)).elim
    · exact hclosed x.1 hx y.1 y.2 hy hxy
  have hwalk : ∀ {x y : (S : Set V)}, (G.induce (S : Set V)).Walk x y →
      x.1 ∈ B → y.1 ∈ B := by
    intro x y p
    induction p with
    | nil => exact id
    | @cons x y z hxy p ih => exact fun hx => ih (hstay x y hx hxy)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨p⟩ := hconn.preconnected ⟨x, hBS hx⟩ ⟨c, hc⟩
  exact hcB (hwalk p hx)

noncomputable def deletedCenterBranch (G : SimpleGraph V) (S : Finset V) (c : V)
    (i : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent) : Finset V := by
  classical
  exact (ForestComponentPartition.componentVertices
    (G.induce ((S.erase c : Finset V) : Set V)) i).image Subtype.val

theorem mem_deletedCenterBranch (G : SimpleGraph V) (S : Finset V) (c : V)
    (i : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent) (x : V) :
    x ∈ deletedCenterBranch G S c i ↔ ∃ hx : x ∈ S.erase c,
      (G.induce ((S.erase c : Finset V) : Set V)).connectedComponentMk ⟨x, hx⟩ = i := by
  classical
  simp only [deletedCenterBranch, mem_image, ForestComponentPartition.mem_componentVertices]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hx, hi⟩
    exact ⟨⟨x, hx⟩, hi, rfl⟩

theorem deletedCenterBranch_subset (G : SimpleGraph V) (S : Finset V) (c : V)
    (i : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent) :
    deletedCenterBranch G S c i ⊆ S.erase c := by
  intro x hx
  exact ((mem_deletedCenterBranch G S c i x).mp hx).choose

theorem deletedCenterBranch_connected (G : SimpleGraph V) (S : Finset V) (c : V)
    (i : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent) :
    (G.induce (deletedCenterBranch G S c i : Set V)).Connected := by
  classical
  let H := G.induce ((S.erase c : Finset V) : Set V)
  let T := ForestComponentPartition.componentVertices H i
  let e : H.induce (T : Set (S.erase c : Set V)) ≃g
      G.induce (deletedCenterBranch G S c i : Set V) :=
    { toFun := fun x => ⟨x.1.1, mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
      invFun := fun x => ⟨⟨x.1, deletedCenterBranch_subset G S c i x.2⟩, by
        apply (ForestComponentPartition.mem_componentVertices H i _).mpr
        exact ((mem_deletedCenterBranch G S c i x.1).mp x.2).choose_spec⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_rel_iff' := by intro x y; rfl }
  exact e.connected_iff.mp (ForestComponentPartition.componentVertices_connected H i)

theorem deletedCenterBranch_nonempty (G : SimpleGraph V) (S : Finset V) (c : V)
    (i : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent) :
    (deletedCenterBranch G S c i).Nonempty := by
  classical
  exact Finset.Nonempty.image
    (ForestComponentPartition.componentVertices_nonempty _ i) _

theorem deletedCenterBranch_closed (G : SimpleGraph V) (S : Finset V) (c : V)
    (i : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent)
    {x y : V} (hx : x ∈ deletedCenterBranch G S c i) (hy : y ∈ S)
    (hyc : y ≠ c) (hxy : G.Adj x y) : y ∈ deletedCenterBranch G S c i := by
  obtain ⟨hx', hxi⟩ := (mem_deletedCenterBranch G S c i x).mp hx
  have hy' : y ∈ S.erase c := mem_erase.mpr ⟨hyc, hy⟩
  have hxy' : (G.induce ((S.erase c : Finset V) : Set V)).Adj ⟨x, hx'⟩ ⟨y, hy'⟩ := hxy
  exact (mem_deletedCenterBranch G S c i y).mpr
    ⟨hy', (ConnectedComponent.eq.mpr hxy'.reachable).symm.trans hxi⟩

theorem deletedCenterBranch_cover (G : SimpleGraph V) (S : Finset V) (c : V) :
    (univ : Finset (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent).biUnion
      (deletedCenterBranch G S c) = S.erase c := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hx
    exact deletedCenterBranch_subset G S c i hi
  · intro hx
    exact mem_biUnion.mpr ⟨_, mem_univ _, (mem_deletedCenterBranch G S c _ x).mpr ⟨hx, rfl⟩⟩

theorem deletedCenterBranch_separated (G : SimpleGraph V) (S : Finset V) (c : V) :
    IsSeparatedFamily G
      (univ : Finset (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent)
      (deletedCenterBranch G S c) := by
  classical
  constructor
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hx', hxi⟩ := (mem_deletedCenterBranch G S c i x).mp hx
    obtain ⟨hy', hxj⟩ := (mem_deletedCenterBranch G S c j x).mp hy
    exact hij (hxi.symm.trans hxj)
  · intro i _ j _ hij x hx y hy hxy
    have hyi := deletedCenterBranch_closed G S c i hx
      (mem_of_mem_erase (deletedCenterBranch_subset G S c j hy))
      (mem_erase.mp (deletedCenterBranch_subset G S c j hy)).1 hxy
    obtain ⟨hy', hyi'⟩ := (mem_deletedCenterBranch G S c i y).mp hyi
    obtain ⟨hy'', hyj⟩ := (mem_deletedCenterBranch G S c j y).mp hy
    exact hij (hyi'.symm.trans hyj)

/-- Every ordinary finite connected forest whose vertices other than c
have degree at most two has a complete actual spider decomposition. -/
theorem exists_spider_of_degree_le_two_off_center (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) {c : V} (hc : c ∈ S)
    (hconn : (G.induce (S : Set V)).Connected)
    (hdeg : ∀ x ∈ S, x ≠ c → degreeOn G S x ≤ 2) :
    ∃ (root tip : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent → V)
      (length : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent → ℕ),
      IsSpiderOn G S c univ (deletedCenterBranch G S c) root tip length := by
  classical
  let B := deletedCenterBranch G S c
  have hnot : ∀ i, c ∉ B i := fun i hi =>
    (mem_erase.mp (deletedCenterBranch_subset G S c i hi)).1 rfl
  have hroot : ∀ i, ∃ r ∈ B i, G.Adj c r := by
    intro i
    exact exists_adj_to_closed_region G S (B i) hc (hnot i)
      ((deletedCenterBranch_subset G S c i).trans (erase_subset _ _))
      (deletedCenterBranch_nonempty G S c i) hconn
      (fun x hx y hy hyc hxy => deletedCenterBranch_closed G S c i hx hy hyc hxy)
  choose root hrootmem hrootadj using hroot
  have hpaths : ∀ i, ∃ u n, PendantPathExtension G {u} u n (B i) (root i) := by
    intro i
    have hsub := deletedCenterBranch_subset G S c i
    have hrootS := mem_of_mem_erase (hsub (hrootmem i))
    have hrootne := (mem_erase.mp (hsub (hrootmem i))).1
    have he := degreeOn_erase_of_adj G S hc (hrootadj i).symm
    have hd := hdeg (root i) hrootS hrootne
    apply exists_pendantPath_to_of_connected_degree_le_two G (B i) (hrootmem i)
      (deletedCenterBranch_connected G S c i)
    · intro x hx
      exact (degreeOn_mono G (hsub.trans (erase_subset _ _)) x).trans
        (hdeg x (mem_of_mem_erase (hsub hx)) (mem_erase.mp (hsub hx)).1)
    · have hm := degreeOn_mono G hsub (root i)
      change degreeOn G (deletedCenterBranch G S c i) (root i) ≤ 1
      omega
  choose tip n hp using hpaths
  refine ⟨root, tip, fun i => n i + 1, ?_⟩
  refine { vertices := ?_
           separated := deletedCenterBranch_separated G S c
           root_mem := fun i _ => hrootmem i
           center_not_mem := fun i _ => hnot i
           center_adj := ?_
           length_pos := fun _ _ => Nat.zero_lt_succ _
           paths := ?_ }
  · rw [deletedCenterBranch_cover, insert_erase hc]
  · intro i _ x hx
    constructor
    · intro hcx
      exact unique_adj_to_connected_region G hG (B i) (hnot i)
        (deletedCenterBranch_connected G S c i) hx (hrootmem i) hcx (hrootadj i)
    · rintro rfl
      exact hrootadj i
  · intro i _
    simpa using hp i

theorem not_minimal_adjustedMean_nonpos_of_degree_le_two_off_center
    (G : SimpleGraph V) (hG : G.IsAcyclic) {S I : Finset V} {c : V}
    (hc : c ∈ S) (hconn : (G.induce (S : Set V)).Connected)
    (hdeg : ∀ x ∈ S, x ≠ c → degreeOn G S x ≤ 2)
    (hI : IsMaximumIndependentOn G S I)
    (hsmaller : ∀ T : Finset V, T ⊆ S → T.card < S.card →
      ∀ K : Finset V, IsMaximumIndependentOn G T K → 0 ≤ adjustedMeanPotential G T K.card) :
    ¬ adjustedMeanPotential G S I.card ≤ 0 := by
  classical
  obtain ⟨root, tip, length, hsp⟩ :=
    exists_spider_of_degree_le_two_off_center G hG S hc hconn hdeg
  exact hsp.not_minimal_adjustedMean_nonpos hI hsmaller

/-- A genuine smallest counterexample must have at least two distinct
branching vertices. This uses ordinary degrees, not an assumed spider form. -/
theorem exists_two_branching_of_minimal_adjustedMean_neg
    (G : SimpleGraph V) (hG : G.IsAcyclic) {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hbad : adjustedMeanPotential G S I.card < 0)
    (hsmaller : ∀ T : Finset V, T ⊆ S → T.card < S.card →
      ∀ K : Finset V, IsMaximumIndependentOn G T K → 0 ≤ adjustedMeanPotential G T K.card) :
    ∃ c ∈ S, ∃ d ∈ S, c ≠ d ∧ 3 ≤ degreeOn G S c ∧ 3 ≤ degreeOn G S d := by
  classical
  have hconn := hI.induce_connected_of_minimal_adjustedMean_neg hbad hsmaller
  have hother : ∀ c ∈ S, ∃ d ∈ S, d ≠ c ∧ 3 ≤ degreeOn G S d := by
    intro c hc
    by_contra! hn
    have hd : ∀ x ∈ S, x ≠ c → degreeOn G S x ≤ 2 := by
      intro x hx hxc
      have hh := hn x hx hxc
      omega
    exact not_minimal_adjustedMean_nonpos_of_degree_le_two_off_center
      G hG hc hconn hd hI hsmaller hbad.le
  obtain ⟨⟨x, hx⟩⟩ := hconn.nonempty
  obtain ⟨c, hc, _, hdc⟩ := hother x hx
  obtain ⟨d, hd, hne, hdd⟩ := hother c hc
  exact ⟨c, hc, d, hd, hne.symm, hdc, hdd⟩

#print axioms unique_adj_to_connected_region
#print axioms exists_adj_to_closed_region
#print axioms deletedCenterBranch_connected
#print axioms exists_spider_of_degree_le_two_off_center
#print axioms exists_two_branching_of_minimal_adjustedMean_neg
end ForestUnimodality
