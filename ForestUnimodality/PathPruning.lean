import ForestUnimodality.AdjustedMeanPath
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Ordinary simple leaf-to-root paths with no internal branching give the
actual pendant extensions used by the adjusted-mean pruning theorem. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

/-- Degree inside a finite induced vertex set, without requiring the whole
ambient vertex type to be finite. -/
noncomputable def degreeOn (G : SimpleGraph V) (S : Finset V) (v : V) : ℕ := by
  classical
  exact (S.filter (G.Adj v)).card

omit [DecidableEq V] in
theorem degreeOn_eq_card_filter (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : degreeOn G S v = (S.filter (G.Adj v)).card := by
  unfold degreeOn
  congr 1
  ext x
  simp

omit [DecidableEq V] in
/-- The relative degree is exactly Mathlib's degree in the induced graph. -/
theorem degreeOn_eq_degree_induce (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {v : V} (hv : v ∈ S) :
    degreeOn G S v = (G.induce (S : Set V)).degree ⟨v, hv⟩ := by
  classical
  have he : ((G.induce (S : Set V)).neighborFinset ⟨v, hv⟩).map
      (Function.Embedding.subtype (· ∈ (S : Set V))) = S.filter (G.Adj v) := by
    ext x
    simp [and_comm]
  rw [degreeOn_eq_card_filter, ← he, card_map]
  rfl

omit [DecidableEq V] in
theorem degreeOn_univ [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    degreeOn G univ v = G.degree v := by
  classical
  have he : univ.filter (G.Adj v) = G.neighborFinset v := by
    ext x
    simp
  rw [degreeOn_eq_card_filter, he]
  rfl

omit [DecidableEq V] in
theorem degreeOn_mono (G : SimpleGraph V) {S T : Finset V} (hST : S ⊆ T) (v : V) :
    degreeOn G S v ≤ degreeOn G T v := by
  classical
  exact card_le_card (filter_subset_filter _ hST)

theorem degreeOn_erase_of_adj (G : SimpleGraph V) (S : Finset V) {v w : V}
    (hw : w ∈ S) (hadj : G.Adj v w) :
    degreeOn G (S.erase w) v + 1 = degreeOn G S v := by
  classical
  unfold degreeOn
  have he : (S.erase w).filter (G.Adj v) = (S.filter (G.Adj v)).erase w := by
    ext x
    simp only [mem_filter, mem_erase]
    tauto
  rw [he]
  exact card_erase_add_one (mem_filter.mpr ⟨hw, hadj⟩)

omit [DecidableEq V] in
theorem adj_eq_of_degreeOn_le_one (G : SimpleGraph V) (S : Finset V) {v w : V}
    (hw : w ∈ S) (hadj : G.Adj v w) (hd : degreeOn G S v ≤ 1) :
    ∀ x ∈ S, G.Adj v x ↔ x = w := by
  classical
  intro x hx
  constructor
  · intro hvx
    exact card_le_one.mp hd x (mem_filter.mpr ⟨hx, hvx⟩) w (mem_filter.mpr ⟨hw, hadj⟩)
  · rintro rfl
    exact hadj

/-- Every ordinary simple path starting at a leaf, with degree at most two
at its internal vertices, is an actual pendant extension of the rest of
the graph. The final/root vertex may have any degree. -/
theorem pendantPathExtension_of_walk {G : SimpleGraph V} {l r : V}
    (p : G.Walk l r) (hp : p.IsPath) (S : Finset V)
    (hs : ∀ x ∈ p.support, x ∈ S)
    (hl : l ≠ r → degreeOn G S l ≤ 1)
    (hi : ∀ x ∈ p.support, x ≠ l → x ≠ r → degreeOn G S x ≤ 2) :
    ∃ H : Finset V, PendantPathExtension G H r p.length S l := by
  classical
  induction p generalizing S with
  | nil =>
    exact ⟨S, PendantPathExtension.zero (hs _ (by simp))⟩
  | @cons l v r hadj p ih =>
    obtain ⟨hp', hnot⟩ := (SimpleGraph.Walk.cons_isPath_iff _ _).mp hp
    have hlS : l ∈ S := hs l (by simp)
    have hvS : v ∈ S := hs v (by simp)
    have hlr : l ≠ r := fun h => hnot (h ▸ p.end_mem_support)
    have hdeg := hl hlr
    have huniq := adj_eq_of_degreeOn_le_one G S hvS hadj hdeg
    have hs' : ∀ x ∈ p.support, x ∈ S.erase l := by
      intro x hx
      refine mem_erase.mpr ⟨?_, hs x (by simp [hx])⟩
      intro hxl
      exact hnot (hxl ▸ hx)
    have hl' : v ≠ r → degreeOn G (S.erase l) v ≤ 1 := by
      intro hvr
      have hv2 := hi v (by simp) hadj.ne.symm hvr
      have he := degreeOn_erase_of_adj G S hlS hadj.symm
      omega
    have hi' : ∀ x ∈ p.support, x ≠ v → x ≠ r → degreeOn G (S.erase l) x ≤ 2 := by
      intro x hx _ hxr
      have hxl : x ≠ l := fun h => hnot (h ▸ hx)
      exact (degreeOn_mono G (erase_subset _ _) x).trans (hi x (by simp [hx]) hxl hxr)
    obtain ⟨H, hH⟩ := ih hp' (S.erase l) hs' hl' hi'
    have hadj' : ∀ x ∈ S.erase l, G.Adj l x ↔ x = v := by
      intro x hx
      exact huniq x (mem_erase.mp hx).2
    have hext := PendantPathExtension.succ hH l (by simp : l ∉ S.erase l) hadj'
    refine ⟨H, ?_⟩
    simpa only [SimpleGraph.Walk.length_cons, insert_erase hlS] using hext

/-- Keep any terminal number of vertices of an actual pendant extension;
the earlier part becomes part of the new host. -/
theorem PendantPathExtension.suffix {G : SimpleGraph V} {H S : Finset V}
    {v u : V} {n : ℕ} (h : PendantPathExtension G H v n S u)
    (k : ℕ) (hk : k ≤ n) :
    ∃ K : Finset V, ∃ w : V, PendantPathExtension G K w k S u := by
  induction h generalizing k with
  | zero hv =>
    have hk0 : k = 0 := by omega
    subst k
    exact ⟨_, _, PendantPathExtension.zero hv⟩
  | @succ n S u h w hw hadj ih =>
    cases k with
    | zero => exact ⟨_, _, PendantPathExtension.zero (mem_insert_self w S)⟩
    | succ k =>
      obtain ⟨K, t, ht⟩ := ih k (by omega)
      exact ⟨K, t, PendantPathExtension.succ ht w hw hadj⟩

/-- The already-proved fourteen-point pruning now applies directly to
ordinary simple paths and actual degree bounds. Every unbranched leg of
a minimal nonpositive adjusted-mean counterexample has at most 13 edges. -/
theorem walk_length_le_thirteen_of_adjustedMean_nonpos
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hbad : adjustedMeanPotential G S I.card ≤ 0)
    (hsmaller : ∀ T : Finset V, T ⊆ S → T.card < S.card →
      ∀ K : Finset V, IsMaximumIndependentOn G T K → 0 ≤ adjustedMeanPotential G T K.card)
    {l r : V} (p : G.Walk l r) (hp : p.IsPath)
    (hs : ∀ x ∈ p.support, x ∈ S)
    (hl : degreeOn G S l ≤ 1)
    (hi : ∀ x ∈ p.support, x ≠ l → x ≠ r → degreeOn G S x ≤ 2) :
    p.length ≤ 13 := by
  by_contra hn
  obtain ⟨H, hH⟩ := pendantPathExtension_of_walk p hp S hs (fun _ => hl) hi
  obtain ⟨K, w, hK⟩ := hH.suffix 14 (by omega)
  exact no_pendantPath_fourteen_of_adjustedMean_nonpos hI hbad hsmaller hK

#print axioms pendantPathExtension_of_walk
#print axioms degreeOn_eq_degree_induce
#print axioms PendantPathExtension.suffix
#print axioms walk_length_le_thirteen_of_adjustedMean_nonpos
end ForestUnimodality
