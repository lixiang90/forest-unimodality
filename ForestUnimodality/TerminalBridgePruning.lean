import ForestUnimodality.TerminalSpiderPruning
import ForestUnimodality.TerminalExceptionalBranches

/-!
Moving a degree-two host root into an actual terminal block creates a
genuine bridge of length two. The checked bridge theorem then excludes it.
The degree-one boundary is treated as a separated component, so no hidden
connectedness assumption on the host is required.
-/

namespace ForestUnimodality

open Finset TerminalBlockRecurrence
universe u v
variable {V : Type u} [DecidableEq V]

omit [DecidableEq V] in
theorem IsRootedBlockAttachment.host_root_not_block
    {G : SimpleGraph V} {H T : Finset V} {p c : V}
    (h : IsRootedBlockAttachment G H p T c) : p ∉ T :=
  fun hpT => disjoint_left.mp h.disjoint h.host_root_mem hpT

theorem IsRootedBlockAttachment.host_root_extension
    {G : SimpleGraph V} {H T : Finset V} {p c : V}
    (h : IsRootedBlockAttachment G H p T c) :
    PendantPathExtension G T c 1 (insert p T) p := by
  apply PendantPathExtension.succ (PendantPathExtension.zero h.block_root_mem)
    p h.host_root_not_block
  intro x hx
  simpa only [eq_self_iff_true, true_and] using h.cross p h.host_root_mem x hx

theorem IsRootedBlockAttachment.move_host_root_vertices
    {G : SimpleGraph V} {H T : Finset V} {p c : V}
    (h : IsRootedBlockAttachment G H p T c) :
    H.erase p ∪ insert p T = H ∪ T := by
  rw [union_insert, ← insert_union, insert_erase h.host_root_mem]

/-- A degree-two host root has one neighbor in the host after its removal;
it can therefore be transferred into the block without changing the graph. -/
theorem IsRootedBlockAttachment.move_host_root_of_degree_two
    {G : SimpleGraph V} {H T : Finset V} {p c : V}
    (h : IsRootedBlockAttachment G H p T c) (hd : degreeOn G (H ∪ T) p = 2) :
    ∃ q, IsRootedBlockAttachment G (H.erase p) q (insert p T) p ∧
      PendantPathExtension G T c 1 (insert p T) p := by
  classical
  have hc : c ∈ H ∪ T := mem_union_right _ h.block_root_mem
  have hpc : G.Adj p c := (h.cross p h.host_root_mem c h.block_root_mem).mpr ⟨rfl, rfl⟩
  have hder := degreeOn_erase_of_adj G (H ∪ T) hc hpc
  have hone : degreeOn G ((H ∪ T).erase c) p = 1 := by omega
  have hpos : 0 < (((H ∪ T).erase c).filter (G.Adj p)).card := by
    rw [← degreeOn_eq_card_filter, hone]
    decide
  obtain ⟨q, hq⟩ := card_pos.mp hpos
  obtain ⟨hqS, hpq⟩ := mem_filter.mp hq
  have hqc : q ≠ c := (mem_erase.mp hqS).1
  have hqH : q ∈ H := by
    rcases mem_union.mp (mem_of_mem_erase hqS) with hqH | hqT
    · exact hqH
    · exact (hqc ((h.cross p h.host_root_mem q hqT).mp hpq).2).elim
  have hqH' : q ∈ H.erase p := mem_erase.mpr ⟨hpq.ne.symm, hqH⟩
  have huniq := adj_eq_of_degreeOn_le_one G ((H ∪ T).erase c) hqS hpq hone.le
  have hd' : Disjoint (H.erase p) (insert p T) := by
    apply disjoint_left.mpr
    intro x hx hy
    rcases mem_insert.mp hy with hxp | hxT
    · exact (mem_erase.mp hx).1 hxp
    · exact disjoint_left.mp h.disjoint (mem_of_mem_erase hx) hxT
  refine ⟨q, ⟨hqH', mem_insert_self _ _, hd', ?_⟩, h.host_root_extension⟩
  intro x hx y hy
  rcases mem_insert.mp hy with rfl | hyT
  · have hxS : x ∈ (H ∪ T).erase c := mem_erase.mpr
      ⟨fun he => h.block_root_not_host (he ▸ mem_of_mem_erase hx),
        mem_union_left _ (mem_of_mem_erase hx)⟩
    simpa only [and_true, eq_self_iff_true, G.adj_comm] using huniq x hxS
  · have hn : ¬ G.Adj x y := by
      intro hadj
      exact (mem_erase.mp hx).1 ((h.cross x (mem_of_mem_erase hx) y hyT).mp hadj).1
    have hyp : y ≠ p := fun he => h.host_root_not_block (he ▸ hyT)
    simp only [hn, hyp, and_false]

variable {ι : Type v} [DecidableEq ι]

theorem IsTerminalSpiderOn.exceptional_legs_of_nonpos
    {G : SimpleGraph V} {S H T : Finset V} {c p : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) (hG : G.IsAcyclic)
    (hsmaller : GlobalSmallerMeanHyp.{u} S.card) (legs : List ℕ)
    (hlegs : (s.toList.map length).Perm legs) (hl : legs ∈ terminalLegs)
    (hbad : adjustedMeanPotential G S (independenceNumberOn G S) ≤ 0) :
    legs = [3,3] ∨ legs = [5,3] := by
  by_contra hn
  have hs : GlobalSmallerMeanHyp.{u} (H ∪ T).card := by rwa [← h.vertices]
  have hp : PendantPathExtension G T c (1 - 1) T c := PendantPathExtension.zero h.attachment.block_root_mem
  have hpos := h.attachment.adjustedMean_pos_of_spiderBridge hG hs h.spider 1 (by decide)
    hp legs hlegs hl (by simpa only [true_and, eq_self_iff_true] using hn)
  rw [← h.vertices] at hpos
  exact (not_lt_of_ge hbad) hpos

/-- The actual terminal block has one of the two exceptional rooted
parameter types. This is a consequence of the checked bridge theorem. -/
theorem IsTerminalSpiderOn.terminal_type_of_nonpos
    {G : SimpleGraph V} {S H T : Finset V} {c p : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) (hG : G.IsAcyclic)
    (hsmaller : GlobalSmallerMeanHyp.{u} S.card) (legs : List ℕ)
    (hlegs : (s.toList.map length).Perm legs) (hl : legs ∈ terminalLegs)
    (hbad : adjustedMeanPotential G S (independenceNumberOn G S) ≤ 0) :
    ∃ i : Fin 8, (i = 0 ∨ i = 1) ∧ InducedIso.BranchParameters G T c i := by
  have hs : GlobalSmallerMeanHyp.{u} (H ∪ T).card := by rwa [← h.vertices]
  have hb : adjustedMeanPotential G (H ∪ T) (independenceNumberOn G (H ∪ T)) ≤ 0 := by
    rwa [← h.vertices]
  exact (h.attachment.terminal_type_of_nonpos hG hs h.spider 1 (by decide)
    (PendantPathExtension.zero h.attachment.block_root_mem) legs hlegs hl hb).2

/-- Moving the actual host root gives bridge length two and hence a
strictly positive full-graph potential. -/
theorem IsTerminalSpiderOn.adjustedMean_pos_of_host_degree_two
    {G : SimpleGraph V} {S H T : Finset V} {c p : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) (hG : G.IsAcyclic)
    (hsmaller : GlobalSmallerMeanHyp.{u} S.card) (legs : List ℕ)
    (hlegs : (s.toList.map length).Perm legs) (hl : legs ∈ terminalLegs)
    (hd : degreeOn G S p = 2) :
    0 < adjustedMeanPotential G S (independenceNumberOn G S) := by
  have hd' : degreeOn G (H ∪ T) p = 2 := by rwa [← h.vertices]
  obtain ⟨q, hatt, hp⟩ := h.attachment.move_host_root_of_degree_two hd'
  have he : H.erase p ∪ insert p T = S := h.attachment.move_host_root_vertices.trans h.vertices.symm
  have hs : GlobalSmallerMeanHyp.{u} (H.erase p ∪ insert p T).card := by rwa [he]
  have hpos := hatt.adjustedMean_pos_of_spiderBridge hG hs h.spider 2 (by decide)
    hp legs hlegs hl (by norm_num)
  rwa [he] at hpos

omit [DecidableEq ι] in
theorem adjustedMeanPotential_eq_actualBlockState (G : SimpleGraph V) (T : Finset V) (c : V) :
    adjustedMeanPotential G T (independenceNumberOn G T) =
      3 * ((actualBlockState G T c).MA + (actualBlockState G T c).MB) /
        ((actualBlockState G T c).A + (actualBlockState G T c).B) -
      (actualBlockState G T c).alpha - (29 / 60 : ℝ) * (actualBlockState G T c).N := by
  simp only [actualBlockState, adjustedMeanPotential, hardCoreMean]
  ring

/-- The two exceptional center-rooted spiders become strictly positive
when one actual pendant vertex is added. This also covers a singleton host. -/
theorem IsSpiderOn.adjustedMean_pos_of_exceptional_singleton_extension
    {G : SimpleGraph V} {S T : Finset V} {c p : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G T c s B root tip length)
    (hp : PendantPathExtension G T c 1 S p) (legs : List ℕ)
    (hlegs : (s.toList.map length).Perm legs) (hl : legs = [3,3] ∨ legs = [5,3]) :
    0 < adjustedMeanPotential G S (independenceNumberOn G S) := by
  have hs := h.actualBlockState_bridgeState_of_perm 2 hp legs hlegs
  rw [adjustedMeanPotential_eq_actualBlockState G S p, hs]
  rcases hl with rfl | rfl <;>
    norm_num [bridgeState, castState, iterate, extend, terminalState,
      ShortLegData.pathData, ShortLegData.transfer]

/-- If the host root has only its attachment edge, the enlarged terminal
block is an entire separated component. Its strict gain handles all other
host components and the singleton-host case uniformly. -/
theorem IsTerminalSpiderOn.adjustedMean_pos_of_host_degree_le_one
    {G : SimpleGraph V} {S H T : Finset V} {c p : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) (hG : G.IsAcyclic)
    (hsmaller : GlobalSmallerMeanHyp.{u} S.card) (legs : List ℕ)
    (hlegs : (s.toList.map length).Perm legs) (hl : legs = [3,3] ∨ legs = [5,3])
    (hd : degreeOn G S p ≤ 1) :
    0 < adjustedMeanPotential G S (independenceNumberOn G S) := by
  have hpT := h.attachment.host_root_not_block
  have hpc : G.Adj p c :=
    (h.attachment.cross p h.attachment.host_root_mem c h.attachment.block_root_mem).mpr ⟨rfl, rfl⟩
  have huniq := adj_eq_of_degreeOn_le_one G S (h.block_subset h.attachment.block_root_mem) hpc hd
  have hdis : Disjoint (H.erase p) (insert p T) := by
    apply disjoint_left.mpr
    intro x hx hy
    rcases mem_insert.mp hy with he | hy
    · exact (mem_erase.mp hx).1 he
    · exact disjoint_left.mp h.attachment.disjoint (mem_of_mem_erase hx) hy
  have hcross : ∀ x ∈ H.erase p, ∀ y ∈ insert p T, ¬ G.Adj x y := by
    intro x hx y hy hxy
    rcases mem_insert.mp hy with rfl | hy
    · have hxc := (huniq x (h.host_subset (mem_of_mem_erase hx))).mp hxy.symm
      exact h.attachment.block_root_not_host (hxc ▸ mem_of_mem_erase hx)
    · exact (mem_erase.mp hx).1 ((h.attachment.cross x (mem_of_mem_erase hx) y hy).mp hxy).1
  have he : H.erase p ∪ insert p T = S := h.attachment.move_host_root_vertices.trans h.vertices.symm
  have hlt : (H.erase p).card < S.card := by
    have hcard := card_union_of_disjoint hdis
    have hpos : 0 < (insert p T).card := card_pos.mpr ⟨p, mem_insert_self _ _⟩
    rw [he] at hcard
    omega
  have hrest := hsmaller V G (H.erase p) hlt hG
  have hblock := h.spider.adjustedMean_pos_of_exceptional_singleton_extension
    h.attachment.host_root_extension legs hlegs hl
  have hadd := adjustedMeanPotential_disjoint_union G (H.erase p) (insert p T) hdis hcross
  rw [he] at hadd
  linarith

/-- A genuine minimal nonpositive terminal configuration must attach
directly to another branching vertex. No connectivity premise is hidden
in this conclusion, and a singleton host is also excluded. -/
theorem IsTerminalSpiderOn.host_degree_ge_three_of_nonpos
    {G : SimpleGraph V} {S H T : Finset V} {c p : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) (hG : G.IsAcyclic)
    (hsmaller : GlobalSmallerMeanHyp.{u} S.card) (legs : List ℕ)
    (hlegs : (s.toList.map length).Perm legs) (hl : legs ∈ terminalLegs)
    (hbad : adjustedMeanPotential G S (independenceNumberOn G S) ≤ 0) :
    3 ≤ degreeOn G S p := by
  by_contra hn
  have hex := h.exceptional_legs_of_nonpos hG hsmaller legs hlegs hl hbad
  have hpos : 0 < adjustedMeanPotential G S (independenceNumberOn G S) := by
    by_cases hd : degreeOn G S p = 2
    · exact h.adjustedMean_pos_of_host_degree_two hG hsmaller legs hlegs hl hd
    · exact h.adjustedMean_pos_of_host_degree_le_one hG hsmaller legs hlegs hex (by omega)
  exact (not_lt_of_ge hbad) hpos

#print axioms IsRootedBlockAttachment.move_host_root_of_degree_two
#print axioms IsTerminalSpiderOn.terminal_type_of_nonpos
#print axioms IsTerminalSpiderOn.adjustedMean_pos_of_host_degree_two
#print axioms IsSpiderOn.adjustedMean_pos_of_exceptional_singleton_extension
#print axioms IsTerminalSpiderOn.adjustedMean_pos_of_host_degree_le_one
#print axioms IsTerminalSpiderOn.host_degree_ge_three_of_nonpos

end ForestUnimodality
