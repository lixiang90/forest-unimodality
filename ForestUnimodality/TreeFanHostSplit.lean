import ForestUnimodality.TreeCenterFan
import ForestUnimodality.TerminalFanAttachment
import ForestUnimodality.TerminalForcedCenter

/-! Split an actual rooted fan at an arbitrary finite set of upward
branches. Keeping at most one upward branch gives exactly the leaf-host
configuration required by the terminal fan closure. -/

namespace ForestUnimodality
open Finset
universe u v
variable {V : Type u} [DecidableEq V]

/-- If every maximum independent set contains a vertex, deleting that
vertex decreases the actual independence number by exactly one. -/
theorem rootDefect_eq_one_of_mem_every_maximum (G : SimpleGraph V) (S : Finset V) (u : V)
    (hforced : ∀ I : Finset V, IsMaximumIndependentOn G S I → u ∈ I) :
    rootDefect G S u = 1 := by
  rcases rootDefect_zero_or_one G S u with hz | hone
  · have hle := (independenceNumberOn_erase_bounds G S u).1
    have he : independenceNumberOn G S = independenceNumberOn G (S.erase u) := by
      unfold rootDefect at hz
      omega
    obtain ⟨I, hI⟩ := exists_maximumIndependentOn G (S.erase u)
    have hmax : IsMaximumIndependentOn G S I := by
      refine ⟨independentSubsets_mono G (erase_subset _ _) hI.1, ?_⟩
      intro J hJ
      rw [hI.card_eq_independenceNumberOn, ← he]
      exact Finset.le_sup hJ
    exact ((mem_erase.mp (hI.subset (hforced I hmax))).1 rfl).elim
  · exact hone

variable {ι : Type v} [DecidableEq ι]

/-- Downward branches with zero root defect do not change the root defect
of the retained host. -/
theorem IsRootedFanAttachment.rootDefect_eq_host
    {G : SimpleGraph V} {S K : Finset V} {u : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanAttachment G S K u s B root)
    (hzero : ∀ i ∈ s, independenceNumberOn G (B i) = independenceNumberOn G ((B i).erase (root i))) :
    rootDefect G S u = rootDefect G K u := by
  have ha := h.independenceNumber_eq hzero
  have he := independenceNumberOn_disjoint_union G (K.erase u) (s.biUnion B)
    (h.disjoint.mono (erase_subset _ _) (Subset.refl _)) h.no_edges_erase_host
  unfold rootDefect
  rw [h.erase_root, ha, he]
  omega

theorem IsRootedFanAttachment.host_rootDefect_eq_one_of_forced
    {G : SimpleGraph V} {S K : Finset V} {u : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanAttachment G S K u s B root)
    (hzero : ∀ i ∈ s, independenceNumberOn G (B i) = independenceNumberOn G ((B i).erase (root i)))
    (hforced : ∀ I : Finset V, IsMaximumIndependentOn G S I → u ∈ I) :
    rootDefect G K u = 1 := by
  rw [← h.rootDefect_eq_host hzero]
  exact rootDefect_eq_one_of_mem_every_maximum G S u hforced

omit [DecidableEq ι] in
theorem IsRootedFanOn.restrict
    {G : SimpleGraph V} {S : Finset V} {u : V}
    {all : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S u all B root) (up : Finset ι) (hup : up ⊆ all) :
    IsRootedFanOn G (insert u (up.biUnion B)) u up B root :=
  { vertices := rfl
    separated := h.separated.mono hup
    root_mem := fun i hi => h.root_mem i (hup hi)
    center_not_mem := fun i hi => h.center_not_mem i (hup hi)
    center_adj := fun i hi => h.center_adj i (hup hi) }

/-- Keep the center and the selected upward branches as the actual host;
every other branch is attached to that host by precisely its original edge. -/
theorem IsRootedFanOn.split_host
    {G : SimpleGraph V} {S : Finset V} {u : V}
    {all : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S u all B root) (up : Finset ι) (hup : up ⊆ all) :
    IsRootedFanAttachment G S (insert u (up.biUnion B)) u (all \ up) B root := by
  refine ⟨?_, mem_insert_self _ _, h.separated.mono sdiff_subset, ?_⟩
  · rw [h.vertices, insert_union, ← union_biUnion, union_sdiff_of_subset hup]
  · intro i hi
    have hiA : i ∈ all := (mem_sdiff.mp hi).1
    have hiU : i ∉ up := (mem_sdiff.mp hi).2
    refine ⟨mem_insert_self _ _, h.root_mem i hiA, ?_, ?_⟩
    · apply disjoint_left.mpr
      intro x hx hxi
      rcases mem_insert.mp hx with rfl | hx
      · exact h.center_not_mem i hiA hxi
      · obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp hx
        have hji : j ≠ i := fun he => hiU (he ▸ hj)
        exact disjoint_left.mp (h.separated.disjoint j (hup hj) i hiA hji) hxj hxi
    · intro x hx y hy
      rcases mem_insert.mp hx with rfl | hx
      · simpa only [eq_self_iff_true, true_and] using h.center_adj i hiA y hy
      · obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp hx
        have hji : j ≠ i := fun he => hiU (he ▸ hj)
        have hn := h.separated.no_edges j (hup hj) i hiA hji x hxj y hy
        have hxu : x ≠ u := fun he => h.center_not_mem j (hup hj) (he ▸ hxj)
        simp only [hn, hxu, false_and]

theorem IsRootedFanOn.degree_split_host
    {G : SimpleGraph V} {S : Finset V} {u : V}
    {all : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S u all B root) (up : Finset ι) (hup : up ⊆ all) :
    degreeOn G (insert u (up.biUnion B)) u = up.card :=
  (h.restrict up hup).degree_center

theorem IsRootedFanOn.degree_split_host_le_one
    {G : SimpleGraph V} {S : Finset V} {u : V}
    {all : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S u all B root) (up : Finset ι) (hup : up ⊆ all)
    (hcard : up.card ≤ 1) : degreeOn G (insert u (up.biUnion B)) u ≤ 1 := by
  rwa [h.degree_split_host up hup]

theorem IsRootedFanOn.down_card_ge_two
    {G : SimpleGraph V} {S : Finset V} {u : V}
    {all : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S u all B root) (up : Finset ι) (hup : up ⊆ all)
    (hcard : up.card ≤ 1) (hdegree : 3 ≤ degreeOn G S u) : 2 ≤ (all \ up).card := by
  have hc := card_sdiff_add_card_eq_card hup
  rw [h.degree_center] at hdegree
  omega

theorem IsRootedFanOn.rootDefect_split_host_eq_one
    {G : SimpleGraph V} {S : Finset V} {u : V}
    {all : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S u all B root) (up : Finset ι) (hup : up ⊆ all)
    (hzero : ∀ i ∈ all \ up,
      independenceNumberOn G (B i) = independenceNumberOn G ((B i).erase (root i)))
    (hforced : ∀ I : Finset V, IsMaximumIndependentOn G S I → u ∈ I) :
    rootDefect G (insert u (up.biUnion B)) u = 1 :=
  (h.split_host up hup).host_rootDefect_eq_one_of_forced hzero hforced

/-- A convenience theorem assembling exactly the actual host configuration
required by the eight-type fan closure, from a finite center fan. -/
theorem IsRootedFanOn.adjustedMean_pos_of_split_eight_types
    {G : SimpleGraph V} {S : Finset V} {u : V}
    {all : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S u all B root) (hG : G.IsAcyclic)
    (hsmaller : GlobalSmallerMeanHyp.{u} S.card) (up : Finset ι) (hup : up ⊆ all)
    (hcard : up.card ≤ 1) (hdegree : 3 ≤ degreeOn G S u) (kind : ι → Fin 8)
    (hp : ∀ i ∈ all \ up, InducedIso.BranchParameters G (B i) (root i) (kind i))
    (ht : ∃ i ∈ all \ up, (kind i).val < 2)
    (hforced : ∀ I : Finset V, IsMaximumIndependentOn G S I → u ∈ I) :
    0 < adjustedMeanPotential G S (independenceNumberOn G S) :=
  (h.split_host up hup).adjustedMean_pos_of_eight_types hG hsmaller kind hp
    (h.down_card_ge_two up hup hcard hdegree) ht
    (h.rootDefect_split_host_eq_one up hup (fun i hi => (hp i hi).root_state_zero) hforced)
    (h.degree_split_host_le_one up hup hcard)

#print axioms rootDefect_eq_one_of_mem_every_maximum
#print axioms IsRootedFanAttachment.rootDefect_eq_host
#print axioms IsRootedFanOn.split_host
#print axioms IsRootedFanOn.degree_split_host
#print axioms IsRootedFanOn.down_card_ge_two
#print axioms IsRootedFanOn.rootDefect_split_host_eq_one
#print axioms IsRootedFanOn.adjustedMean_pos_of_split_eight_types
end ForestUnimodality
