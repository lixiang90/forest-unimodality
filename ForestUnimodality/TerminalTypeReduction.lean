import ForestUnimodality.TerminalLegClassification
import ForestUnimodality.TerminalLegCluster
import ForestUnimodality.TerminalBridgePruning

/-! Full actual-graph terminal type reduction. No leg-length, parity,
branch-count, numerical state, or canonical-list premise is left to callers. -/
namespace ForestUnimodality
open Finset TerminalBlockRecurrence
universe u
variable {V : Type u} {ι : Type*} [DecidableEq V] [DecidableEq ι]
variable {G : SimpleGraph V} {S H T : Finset V} {c p : V}
  {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}

theorem IsTerminalSpiderOn.center_host_card_lt
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) : (insert c H).card < S.card := by
  have hsub : insert c H ⊆ S := insert_subset
    (h.block_subset h.attachment.block_root_mem) h.host_subset
  obtain ⟨i, hi⟩ := card_pos.mp (show 0 < s.card by have hh := h.branches; omega)
  have htipB := (h.spider.paths i hi).host_subset (mem_singleton_self _)
  have htipT := h.branch_subset_block hi htipB
  have htipnot : tip i ∉ insert c H := by
    intro ht
    rcases mem_insert.mp ht with he | ht
    · exact h.spider.center_not_mem i hi (he ▸ htipB)
    · exact disjoint_left.mp h.attachment.disjoint ht htipT
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro he
  exact htipnot (he.symm ▸ h.tip_mem hi)

theorem IsTerminalSpiderOn.legs_mem_terminal_of_nonpos
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) (hG : G.IsAcyclic)
    (hsmaller : GlobalSmallerMeanHyp.{u} S.card)
    (hbad : adjustedMeanPotential G S (independenceNumberOn G S) ≤ 0) :
    ∃ legs ∈ terminalLegs, (s.toList.map length).Perm legs := by
  classical
  obtain ⟨I, hI⟩ := exists_maximumIndependentOn G S
  have hbadI : adjustedMeanPotential G S I.card ≤ 0 := by rwa [hI.card_eq_independenceNumberOn]
  have hlocal := hsmaller.same_graph G hG S rfl
  have hshort := fun i hi => h.leg_length_le_thirteen_of_minimal_adjustedMean_nonpos
    hI hbadI hlocal (i := i) hi
  have hsame := h.same_parity_of_minimal_adjustedMean_nonpos hI hbadI hlocal
  obtain ⟨i, hi⟩ := card_pos.mp (show 0 < s.card by have hh := h.branches; omega)
  have hpar : ∃ odd : Bool, ∀ j ∈ s, length j % 2 = if odd then 1 else 0 := by
    by_cases he : length i % 2 = 0
    · exact ⟨false, fun j hj => (hsame j hj i hi).trans he⟩
    · have ho : length i % 2 = 1 := by have hm := Nat.mod_lt (length i) (by decide : 0 < 2); omega
      exact ⟨true, fun j hj => (hsame j hj i hi).trans ho⟩
  obtain ⟨odd, hpar⟩ := hpar
  have hK := hsmaller V G (insert c H) h.center_host_card_lt hG
  have hH := hsmaller V G H
    (lt_of_le_of_lt (card_le_card (subset_insert _ _)) h.center_host_card_lt) hG
  have hm := h.card_le_three_of_short_sameParity_nonpos hshort odd hpar hK hH hbad
  have hlo := h.branches
  have hlen : (s.toList.map length).length = 2 ∨ (s.toList.map length).length = 3 := by
    simp only [List.length_map, length_toList]
    omega
  have hd : rootDefect G (insert c H) c ≤ 1 := by
    rcases rootDefect_zero_or_one G (insert c H) c with he | he <;> omega
  have hr := h.center_ratio_bounds
  have hclass := ShortLegData.short_legs_classification odd (s.toList.map length)
    (rootDefect G (insert c H) c) hlen
    (by intro l hl; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
        exact h.spider.length_pos j (mem_toList.mp hj))
    (by intro l hl; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
        exact hshort j (mem_toList.mp hj))
    (by intro l hl; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
        exact hpar j (mem_toList.mp hj)) hd _ hr.1 hr.2
  rcases hclass with he | hres
  · exact he
  · exact ((not_lt_of_ge hbad) (h.adjustedMean_pos_of_leg_residual odd hpar hK hH hres)).elim

/-- Every actual terminal in a smallest nonpositive forest is an actual
T33 or T35 parameter type, directly adjacent to another branching vertex. -/
theorem IsTerminalSpiderOn.two_types_and_branching_host_of_nonpos
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) (hG : G.IsAcyclic)
    (hsmaller : GlobalSmallerMeanHyp.{u} S.card)
    (hbad : adjustedMeanPotential G S (independenceNumberOn G S) ≤ 0) :
    (∃ i : Fin 8, (i = 0 ∨ i = 1) ∧ InducedIso.BranchParameters G T c i) ∧
      3 ≤ degreeOn G S p := by
  obtain ⟨legs, hl, hlegs⟩ := h.legs_mem_terminal_of_nonpos hG hsmaller hbad
  exact ⟨h.terminal_type_of_nonpos hG hsmaller legs hlegs hl hbad,
    h.host_degree_ge_three_of_nonpos hG hsmaller legs hlegs hl hbad⟩

#print axioms IsTerminalSpiderOn.legs_mem_terminal_of_nonpos
#print axioms IsTerminalSpiderOn.two_types_and_branching_host_of_nonpos
end ForestUnimodality
