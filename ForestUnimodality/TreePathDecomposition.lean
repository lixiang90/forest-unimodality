import ForestUnimodality.PathPruning
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Actual path witnesses for connected finite induced graphs with maximum
degree two and a specified endpoint. This is a structural coverage theorem,
not a numerical assumption about a path's statistics. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

theorem connected_induce_erase_of_degree_one (G : SimpleGraph V) (S : Finset V)
    {r : V} (hr : r ∈ S) (hconn : (G.induce (S : Set V)).Connected)
    (hdeg : degreeOn G S r = 1) : (G.induce ((S.erase r : Finset V) : Set V)).Connected := by
  classical
  let H := G.induce (S : Set V)
  let rS : (S : Set V) := ⟨r, hr⟩
  have hdeg' : H.degree rS = 1 := by
    rw [← degreeOn_eq_degree_induce G S hr]
    exact hdeg
  have hc := hconn.induce_compl_singleton_of_degree_eq_one hdeg'
  let e : H.induce ({rS}ᶜ : Set (S : Set V)) ≃g
      G.induce ((S.erase r : Finset V) : Set V) :=
    { toFun := fun x => ⟨x.1.1, mem_erase.mpr ⟨by
        intro hx
        apply x.2
        exact Set.mem_singleton_iff.mpr (Subtype.ext hx), x.1.2⟩⟩
      invFun := fun x => ⟨⟨x.1, (mem_erase.mp x.2).2⟩, by
        intro hx
        apply (mem_erase.mp x.2).1
        exact congrArg Subtype.val (Set.mem_singleton_iff.mp hx)⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_rel_iff' := by intro x y; rfl }
  exact e.connected_iff.mp hc

/-- A connected degree-at-most-two graph, viewed from any vertex of degree
at most one, is a genuine path grown from a singleton at the other end. -/
theorem exists_pendantPath_to_of_connected_degree_le_two
    (G : SimpleGraph V) (S : Finset V) {r : V} (hr : r ∈ S)
    (hconn : (G.induce (S : Set V)).Connected)
    (hdegrees : ∀ x ∈ S, degreeOn G S x ≤ 2) (hrdeg : degreeOn G S r ≤ 1) :
    ∃ u n, PendantPathExtension G {u} u n S r := by
  classical
  induction S using Finset.strongInductionOn generalizing r
  rename_i S ih
  by_cases he : S = {r}
  · subst S
    exact ⟨r, 0, PendantPathExtension.zero (by simp)⟩
  · have hother : ∃ x ∈ S, x ≠ r := by
      by_contra! hn
      apply he
      ext x
      simp only [mem_singleton]
      exact ⟨fun hx => hn x hx, fun h => h ▸ hr⟩
    obtain ⟨x, hx, hxr⟩ := hother
    let rS : (S : Set V) := ⟨r, hr⟩
    let xS : (S : Set V) := ⟨x, hx⟩
    have hne : rS ≠ xS := fun h => hxr (congrArg Subtype.val h).symm
    obtain ⟨v, hrv⟩ := (hconn.preconnected rS xS).nonempty_neighborSet_left hne
    have hv : v.1 ∈ S := v.2
    have hadj : G.Adj r v.1 := hrv
    have hv' : v.1 ∈ S.erase r := mem_erase.mpr ⟨hadj.ne.symm, hv⟩
    have hpos : 1 ≤ degreeOn G S r := by
      apply Nat.succ_le_iff.mpr
      exact card_pos.mpr ⟨v.1, mem_filter.mpr ⟨hv, hadj⟩⟩
    have hdeg : degreeOn G S r = 1 := by omega
    have hc := connected_induce_erase_of_degree_one G S hr hconn hdeg
    have hvdeg : degreeOn G (S.erase r) v.1 ≤ 1 := by
      have ha := degreeOn_erase_of_adj G S hr hadj.symm
      have hb := hdegrees v.1 hv
      omega
    obtain ⟨u, n, hp⟩ := ih (S.erase r) (erase_ssubset hr) hv' hc
      (fun y hy => (degreeOn_mono G (erase_subset _ _) y).trans (hdegrees y (mem_of_mem_erase hy))) hvdeg
    have huniq := adj_eq_of_degreeOn_le_one G S hv hadj hrdeg
    refine ⟨u, n + 1, ?_⟩
    have hp' := PendantPathExtension.succ hp r (by simp : r ∉ S.erase r)
      (fun y hy => huniq y (mem_of_mem_erase hy))
    simpa only [insert_erase hr] using hp'

#print axioms connected_induce_erase_of_degree_one
#print axioms exists_pendantPath_to_of_connected_degree_le_two
end ForestUnimodality
