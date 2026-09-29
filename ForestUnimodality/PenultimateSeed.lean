import ForestUnimodality.PenultimateBranchTypes

/-! A real penultimate branching vertex extracted from a smallest negative
forest, retaining the terminal witness and the global depth bound. -/
namespace ForestUnimodality
open Finset
universe u
variable {V : Type u} [DecidableEq V]

structure IsPenultimateSeed (G : SimpleGraph V) (S : Finset V) (r u c : V)
    (H T : Finset V) : Prop where
  vertices : S = H ∪ T
  upstream_mem : r ∈ H
  host_connected : (G.induce (H : Set V)).Connected
  attachment : IsRootedBlockAttachment G H u T c
  terminal : ∃ i : Fin 8, (i = 0 ∨ i = 1) ∧ InducedIso.BranchParameters G T c i
  branching : 3 ≤ degreeOn G S u
  depth_eq : G.dist r c = G.dist r u + 1
  depth_bound : ∀ x ∈ S, 3 ≤ degreeOn G S x → G.dist r x ≤ G.dist r u + 1

theorem exists_penultimate_seed_of_minimal_neg (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (hsmaller : GlobalSmallerMeanHyp.{u} S.card)
    (hbad : adjustedMeanPotential G S (independenceNumberOn G S) < 0) :
    ∃ r u c H T, IsPenultimateSeed G S r u c H T := by
  classical
  obtain ⟨I, hI⟩ := exists_maximumIndependentOn G S
  have hbadI : adjustedMeanPotential G S I.card < 0 := by rwa [hI.card_eq_independenceNumberOn]
  have hlocal := hsmaller.same_graph G hG S rfl
  have hconn := hI.induce_connected_of_minimal_adjustedMean_neg hbadI hlocal
  obtain ⟨r, hr, d, hd, hrd, _, hdd⟩ :=
    exists_two_branching_of_minimal_adjustedMean_neg G hG hI hbadI hlocal
  obtain ⟨c, _, _, H, T, p, root, tip, len, ht, hrH, hHconn, hmax⟩ :=
    exists_farthest_terminal_spider G hG S hconn hr hd hrd.symm hdd
  have htypes := ht.two_types_and_branching_host_of_nonpos hG hsmaller hbad.le
  have hdepth := ht.attachment.dist_block_root hG hHconn hrH
  refine ⟨r, p, c, H, T, ht.vertices, hrH, hHconn, ht.attachment, htypes.1, htypes.2, hdepth, ?_⟩
  intro x hx hxd
  simpa only [hdepth] using hmax x hx hxd

#print axioms exists_penultimate_seed_of_minimal_neg
end ForestUnimodality
