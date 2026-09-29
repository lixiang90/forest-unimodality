import ForestUnimodality.TreeSpiderDecomposition
import ForestUnimodality.UnitActivityPathDensity

/-! Actual rooted branch decompositions and exact unit-activity mixture
statistics.  These interfaces concern the original graph vertex sets. -/
namespace ForestUnimodality
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem exists_rootedFan_of_tree (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) {c : V} (hc : c ∈ S)
    (hconn : (G.induce (S : Set V)).Connected) :
    ∃ root : (G.induce ((S.erase c : Finset V) : Set V)).ConnectedComponent → V,
      IsRootedFanOn G S c univ (deletedCenterBranch G S c) root := by
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
  refine ⟨root, ?_⟩
  refine { vertices := ?_
           separated := deletedCenterBranch_separated G S c
           root_mem := fun i _ => hrootmem i
           center_not_mem := fun i _ => hnot i
           center_adj := ?_ }
  · rw [deletedCenterBranch_cover, insert_erase hc]
  · intro i _ x hx
    constructor
    · intro hcx
      exact unique_adj_to_connected_region G hG (B i) (hnot i)
        (deletedCenterBranch_connected G S c i) hx (hrootmem i) hcx (hrootadj i)
    · rintro rfl
      exact hrootadj i

variable {ι : Type*} [DecidableEq ι]

theorem IsRootedFanOn.unitActivity_degree_center {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) : degreeOn G S c = s.card := by
  classical
  have hinj : Set.InjOn root (s : Set ι) := by
    intro i hi j hj he
    by_contra hne
    exact disjoint_left.mp (h.separated.disjoint i hi j hj hne)
      (h.root_mem i hi) (he ▸ h.root_mem j hj)
  have heq : S.filter (G.Adj c) = s.image root := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxS, hcx⟩ := mem_filter.mp hx
      rw [h.vertices] at hxS
      rcases mem_insert.mp hxS with hx | hx
      · exact (hcx.ne hx.symm).elim
      · obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx
        exact mem_image.mpr ⟨i, hi, ((h.center_adj i hi x hxi).mp hcx).symm⟩
    · intro hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      refine mem_filter.mpr ⟨?_, (h.center_adj i hi _ (h.root_mem i hi)).mpr rfl⟩
      rw [h.vertices]
      exact mem_insert_of_mem (mem_biUnion.mpr ⟨i, hi, h.root_mem i hi⟩)
  rw [degreeOn_eq_card_filter, heq, card_image_of_injOn hinj]

theorem IsRootedFanOn.unitActivity_mean_mixture
    {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) :
    let r := 1 / (1 + ∏ i ∈ s,
      partitionFunction G ((B i).erase (root i)) (1 : ℝ) / partitionFunction G (B i) 1)
    hardCoreMean G S 1 = r * (∑ i ∈ s, hardCoreMean G (B i) 1) +
      (1 - r) * (1 + ∑ i ∈ s, hardCoreMean G ((B i).erase (root i)) 1) := by
  have ha : 0 < ∏ i ∈ s, partitionFunction G (B i) (1 : ℝ) := by
    exact Finset.prod_pos (fun _ _ => partitionFunction_pos _ _ (by norm_num))
  have hb : 0 < ∏ i ∈ s, partitionFunction G ((B i).erase (root i)) (1 : ℝ) := by
    exact Finset.prod_pos (fun _ _ => partitionFunction_pos _ _ (by norm_num))
  dsimp only
  rw [Finset.prod_div_distrib]
  change hardCoreMomentNumerator G S 1 1 / partitionFunction G S 1 = _
  rw [h.firstMoment (by norm_num : (0 : ℝ) ≤ 1), h.partitionFunction_eq G 1]
  simp only [one_mul]
  have hab := ne_of_gt (add_pos ha hb)
  field_simp
  ring

#print axioms exists_rootedFan_of_tree
#print axioms IsRootedFanOn.unitActivity_degree_center
#print axioms IsRootedFanOn.unitActivity_mean_mixture
end ForestUnimodality
