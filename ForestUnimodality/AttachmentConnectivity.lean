import ForestUnimodality.TreeCenterFan

/-! Connectivity of real blocks separated from the rest at one root. -/
namespace ForestUnimodality
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]

theorem connected_region_of_single_exit (G : SimpleGraph V) (S B : Finset V)
    {w : V} (hw : w ∈ B) (hBS : B ⊆ S)
    (hconn : (G.induce (S : Set V)).Connected)
    (hexit : ∀ x ∈ B, ∀ y ∈ S, y ∉ B → G.Adj x y → x = w) :
    (G.induce (B : Set V)).Connected := by
  classical
  have hwalk : ∀ {x : V} (q : G.Walk x w), q.IsPath →
      (∀ z ∈ q.support, z ∈ S) → x ∈ B → ∀ z ∈ q.support, z ∈ B := by
    intro x q
    induction q with
    | @nil a =>
      intro _ _ _ z hz
      have he : z = a := by simpa using hz
      exact he ▸ hw
    | @cons x y w hxy q ih =>
      intro hpath hsub hx z hz
      have hyS := hsub y (by simp)
      have hyB : y ∈ B := by
        by_contra hy
        have hxw := hexit x hx y hyS hy hxy
        have hnot := (Walk.cons_isPath_iff hxy q).mp hpath |>.2
        exact hnot (hxw ▸ q.end_mem_support)
      have htail := ih hw hexit hpath.of_cons (fun z hz => hsub z (by simp [hz])) hyB
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx
      · exact htail z hz
  let wB : (B : Set V) := ⟨w, hw⟩
  have hreach : ∀ x : (B : Set V), (G.induce (B : Set V)).Reachable x wB := by
    intro x
    let f : G.induce (S : Set V) →g G := ⟨Subtype.val, fun h => h⟩
    obtain ⟨q, hq⟩ := (hconn.preconnected ⟨x.1, hBS x.2⟩ ⟨w, hBS hw⟩).exists_isPath
    have hq' : (q.map f).IsPath := hq.map Subtype.val_injective
    have hs : ∀ z ∈ (q.map f).support, z ∈ S := by
      intro z hz
      rw [Walk.support_map] at hz
      obtain ⟨y, _, hy⟩ := List.mem_map.mp hz
      exact hy ▸ y.2
    have hb := hwalk (q.map f) hq' hs x.2
    exact ((q.map f).induce (B : Set V) hb).reachable
  exact { preconnected := fun x y => (hreach x).trans (hreach y).symm
          nonempty := ⟨wB⟩ }

theorem IsRootedBlockAttachment.block_connected {G : SimpleGraph V}
    {H T : Finset V} {p c : V} (h : IsRootedBlockAttachment G H p T c)
    (hconn : (G.induce ((H ∪ T : Finset V) : Set V)).Connected) :
    (G.induce (T : Set V)).Connected := by
  apply connected_region_of_single_exit G (H ∪ T) T h.block_root_mem subset_union_right hconn
  intro x hx y hy hyT hxy
  have hyH := (mem_union.mp hy).resolve_right hyT
  exact ((h.cross y hyH x hx).mp hxy.symm).2

theorem IsRootedBlockAttachment.host_connected {G : SimpleGraph V}
    {H T : Finset V} {p c : V} (h : IsRootedBlockAttachment G H p T c)
    (hconn : (G.induce ((H ∪ T : Finset V) : Set V)).Connected) :
    (G.induce (H : Set V)).Connected := by
  apply connected_region_of_single_exit G (H ∪ T) H h.host_root_mem subset_union_left hconn
  intro x hx y hy hyH hxy
  have hyT := (mem_union.mp hy).resolve_left hyH
  exact ((h.cross x hx y hyT).mp hxy).1

#print axioms connected_region_of_single_exit
#print axioms IsRootedBlockAttachment.block_connected
#print axioms IsRootedBlockAttachment.host_connected
end ForestUnimodality
