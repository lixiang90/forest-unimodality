import ForestUnimodality.AttachmentConnectivity

/-! A real one-edge block is precisely its component after deleting the
host root. This identification requires connectivity, but no acyclicity. -/
namespace ForestUnimodality
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

namespace IsRootedBlockAttachment
variable {G : SimpleGraph V} {H T : Finset V} {u c : V}
    (h : IsRootedBlockAttachment G H u T c)
include h

theorem block_subset_erase_host_root : T ⊆ (H ∪ T).erase u := by
  intro x hx
  exact mem_erase.mpr ⟨fun he => disjoint_left.mp h.disjoint h.host_root_mem (he ▸ hx),
    mem_union_right H hx⟩

noncomputable def blockComponent :
    (G.induce (((H ∪ T).erase u : Finset V) : Set V)).ConnectedComponent :=
  (G.induce (((H ∪ T).erase u : Finset V) : Set V)).connectedComponentMk
    ⟨c, h.block_subset_erase_host_root h.block_root_mem⟩

theorem block_eq_deletedCenterBranch
    (hconn : (G.induce ((H ∪ T : Finset V) : Set V)).Connected) :
    T = deletedCenterBranch G (H ∪ T) u h.blockComponent := by
  let Q := G.induce (((H ∪ T).erase u : Finset V) : Set V)
  let f : G.induce (T : Set V) →g Q :=
    ⟨fun x => ⟨x.1, h.block_subset_erase_host_root x.2⟩, fun hxy => hxy⟩
  have hwalk : ∀ {x y : ((H ∪ T).erase u : Set V)} (p : Q.Walk x y),
      x.1 ∈ T → y.1 ∈ T := by
    intro x y p
    induction p with
    | nil => exact id
    | @cons x y z hxy p ih =>
      intro hx
      apply ih
      by_contra hy
      have hyH := (mem_union.mp (mem_of_mem_erase y.2)).resolve_right hy
      have hyu := ((h.cross y.1 hyH x.1 hx).mp (show G.Adj y.1 x.1 from hxy.symm)).1
      exact (mem_erase.mp y.2).1 hyu
  ext x
  constructor
  · intro hx
    apply (mem_deletedCenterBranch G (H ∪ T) u h.blockComponent x).mpr
    refine ⟨h.block_subset_erase_host_root hx, ?_⟩
    exact ConnectedComponent.eq.mpr
      (((h.block_connected hconn).preconnected ⟨x, hx⟩ ⟨c, h.block_root_mem⟩).map f)
  · intro hx
    obtain ⟨hx', hxc⟩ := (mem_deletedCenterBranch G (H ∪ T) u h.blockComponent x).mp hx
    have hr : Q.Reachable ⟨c, h.block_subset_erase_host_root h.block_root_mem⟩ ⟨x, hx'⟩ :=
      (ConnectedComponent.eq.mp hxc).symm
    exact hwalk hr.some h.block_root_mem

theorem component_fan_root_eq
    (hconn : (G.induce ((H ∪ T : Finset V) : Set V)).Connected)
    (root : (G.induce (((H ∪ T).erase u : Finset V) : Set V)).ConnectedComponent → V)
    (hfan : IsRootedFanOn G (H ∪ T) u univ (deletedCenterBranch G (H ∪ T) u) root) :
    root h.blockComponent = c := by
  have hc : c ∈ deletedCenterBranch G (H ∪ T) u h.blockComponent := by
    rw [← h.block_eq_deletedCenterBranch hconn]
    exact h.block_root_mem
  have huc := (h.cross u h.host_root_mem c h.block_root_mem).mpr ⟨rfl, rfl⟩
  exact ((hfan.center_adj h.blockComponent (mem_univ _) c hc).mp huc).symm

theorem blockComponent_ne_hostComponent
    (hconn : (G.induce ((H ∪ T : Finset V) : Set V)).Connected)
    {r : V} (hr : r ∈ H) (hru : r ≠ u) :
    h.blockComponent ≠
      (G.induce (((H ∪ T).erase u : Finset V) : Set V)).connectedComponentMk
        ⟨r, mem_erase.mpr ⟨hru, mem_union_left T hr⟩⟩ := by
  intro he
  have hrB : r ∈ deletedCenterBranch G (H ∪ T) u h.blockComponent :=
    (mem_deletedCenterBranch G (H ∪ T) u h.blockComponent r).mpr
      ⟨mem_erase.mpr ⟨hru, mem_union_left T hr⟩, he.symm⟩
  rw [← h.block_eq_deletedCenterBranch hconn] at hrB
  exact disjoint_left.mp h.disjoint hr hrB

end IsRootedBlockAttachment
#print axioms IsRootedBlockAttachment.block_eq_deletedCenterBranch
#print axioms IsRootedBlockAttachment.component_fan_root_eq
#print axioms IsRootedBlockAttachment.blockComponent_ne_hostComponent
end ForestUnimodality
