import ForestUnimodality.TreeCenterFan
import ForestUnimodality.TerminalTypeReduction
import ForestUnimodality.TerminalForcedCenter
import ForestUnimodality.EvenPathBranchParameters

/-! Actual branches at the penultimate depth: terminal types or short paths. -/
namespace ForestUnimodality
open Finset
universe u
variable {V : Type u} {ι : Type*} [DecidableEq V] [DecidableEq ι]

theorem IsRootedBlockAttachment.whole_path_of_singleton_block
    {G : SimpleGraph V} {H B : Finset V} {c w v : V} {n : ℕ}
    (h : IsRootedBlockAttachment G H c B w)
    (hp : PendantPathExtension G {v} v n B w) :
    PendantPathExtension G H c (n + 1) (H ∪ B) v := by
  apply hp.reverse_attach H c h.host_root_mem h.disjoint
  intro x hx y hy
  simpa only [G.adj_comm, and_comm] using h.cross y hy x hx

omit [DecidableEq ι] in
theorem IsRootedFanOn.branch_types_of_nonpos
    {G : SimpleGraph V} (hG : G.IsAcyclic) {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root)
    (hsmaller : GlobalSmallerMeanHyp.{u} S.card)
    (hbad : adjustedMeanPotential G S (independenceNumberOn G S) ≤ 0)
    {i : ι} (hi : i ∈ s) (hconn : (G.induce (B i : Set V)).Connected)
    (hadj : ∀ x ∈ B i, 3 ≤ degreeOn G S x → G.Adj c x) :
    (∃ j : Fin 8, (j = 0 ∨ j = 1) ∧ InducedIso.BranchParameters G (B i) (root i) j) ∨
      ∃ v n, PendantPathExtension G {v} v n (B i) (root i) ∧ n + 1 ≤ 13 := by
  classical
  by_cases hb : ∃ x ∈ B i, 3 ≤ degreeOn G S x
  · obtain ⟨x, hx, hxd⟩ := hb
    have he := (h.center_adj i hi x hx).mp (hadj x hx hxd)
    have hroot : 3 ≤ degreeOn G S (root i) := he ▸ hxd
    have hdeg : ∀ y ∈ B i, y ≠ root i → degreeOn G S y ≤ 2 := by
      intro y hy hyr
      by_contra! hn
      exact hyr ((h.center_adj i hi y hy).mp (hadj y hy (by omega)))
    obtain ⟨rt, tp, len, ht⟩ := h.exists_terminal_on_branch hG hi hconn hroot hdeg
    exact Or.inl (ht.two_types_and_branching_host_of_nonpos hG hsmaller hbad).1
  · have hdeg : ∀ x ∈ B i, degreeOn G S x ≤ 2 := by
      intro x hx
      by_contra! hn
      exact hb ⟨x, hx, by omega⟩
    have hrootdeg : degreeOn G (B i) (root i) ≤ 1 := by
      have he := h.degree_branch_root hi
      have hd := hdeg (root i) (h.root_mem i hi)
      omega
    obtain ⟨v, n, hp⟩ := exists_pendantPath_to_of_connected_degree_le_two G (B i)
      (h.root_mem i hi) hconn
      (fun x hx => (degreeOn_mono G (h.branch_subset hi) x).trans (hdeg x hx)) hrootdeg
    refine Or.inr ⟨v, n, hp, ?_⟩
    by_contra! hn
    have hw := (h.branch_attachment hi).whole_path_of_singleton_block hp
    rw [sdiff_union_of_subset (h.branch_subset hi)] at hw
    obtain ⟨A, w, hlong⟩ := hw.suffix 14 (by omega)
    obtain ⟨I, hI⟩ := exists_maximumIndependentOn G S
    have hbadI : adjustedMeanPotential G S I.card ≤ 0 := by rwa [hI.card_eq_independenceNumberOn]
    exact no_pendantPath_fourteen_of_adjustedMean_nonpos hI hbadI
      (hsmaller.same_graph G hG S rfl) hlong

omit [DecidableEq ι] in
theorem IsRootedFanOn.eight_branch_types_of_forced_center
    {G : SimpleGraph V} (hG : G.IsAcyclic) {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root)
    (hsmaller : GlobalSmallerMeanHyp.{u} S.card)
    (hbad : adjustedMeanPotential G S (independenceNumberOn G S) ≤ 0)
    (hc : ∀ I, IsMaximumIndependentOn G S I → c ∈ I)
    {i : ι} (hi : i ∈ s) (hconn : (G.induce (B i : Set V)).Connected)
    (hadj : ∀ x ∈ B i, 3 ≤ degreeOn G S x → G.Adj c x) :
    ∃ j : Fin 8, InducedIso.BranchParameters G (B i) (root i) j := by
  rcases h.branch_types_of_nonpos hG hsmaller hbad hi hconn hadj with ht | hp
  · obtain ⟨j, _, hj⟩ := ht
    exact ⟨j, hj⟩
  · obtain ⟨v, n, hp, hshort⟩ := hp
    have he : S \ B i ∪ B i = S := sdiff_union_of_subset (h.branch_subset hi)
    have heven := (h.branch_attachment hi).path_order_even_of_nonpos hp hG
      (he.symm ▸ hsmaller) (he.symm ▸ hbad) (he.symm ▸ hc)
    obtain ⟨j, _, hj⟩ := hp.even_branchParameters hshort heven
    exact ⟨j, hj⟩

#print axioms IsRootedBlockAttachment.whole_path_of_singleton_block
#print axioms IsRootedFanOn.branch_types_of_nonpos
#print axioms IsRootedFanOn.eight_branch_types_of_forced_center
end ForestUnimodality
