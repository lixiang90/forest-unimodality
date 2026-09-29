import ForestUnimodality.EdgeLowerBound
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! The unordered endpoint-pair edge count agrees with mathlib's induced
graph edge finset. This connects the counting row to structural graph bounds. -/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- Counting adjacent endpoint pairs is exactly counting edges of the induced graph. -/
theorem edgeCountOn_eq_card_edgeFinset_induce
    (G : SimpleGraph V) (S : Finset V) [DecidableRel G.Adj] :
    edgeCountOn G S = (G.induce (↑S : Set V)).edgeFinset.card := by
  classical
  let H := G.induce (↑S : Set V)
  let f : Sym2 (↑S : Set V) → Finset V := fun e => e.toFinset.image Subtype.val
  have hfinj : Function.Injective f := by
    intro e e' he
    have he' : e.toFinset = e'.toFinset :=
      Finset.image_injective Subtype.val_injective he
    apply Sym2.ext
    intro x
    simpa only [Sym2.mem_toFinset] using
      Iff.of_eq (congrArg (fun T : Finset (↑S : Set V) => x ∈ T) he')
  have hmem : ∀ e ∈ H.edgeFinset, f e ∈ edgePairsOn G S := by
    intro e
    induction e using Sym2.ind with
    | _ x y =>
      intro he
      have hxy : G.Adj x.val y.val := (H.mem_edgeFinset).mp he
      simp only [f, Sym2.toFinset_mk_eq, image_insert, image_singleton]
      apply mem_edgePairsOn.mpr
      refine ⟨insert_subset x.property (singleton_subset_iff.mpr y.property), ?_, ?_⟩
      · simp [hxy.ne]
      · intro hind
        exact hind (by simp) (by simp) hxy.ne hxy
  have himage : H.edgeFinset.image f = edgePairsOn G S := by
    ext E
    constructor
    · intro hE
      obtain ⟨e, he, rfl⟩ := mem_image.mp hE
      exact hmem e he
    · intro hE
      obtain ⟨hES, hEcard, hbad⟩ := mem_edgePairsOn.mp hE
      obtain ⟨x, y, hxyne, rfl⟩ := card_eq_two.mp hEcard
      have hxS : x ∈ S := hES (by simp)
      have hyS : y ∈ S := hES (by simp)
      have hxy : G.Adj x y := by
        by_contra hn
        apply hbad
        intro a ha b hb hab
        simp only [mem_coe, mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact (hab rfl).elim
        · exact hn
        · exact fun hyx => hn hyx.symm
        · exact (hab rfl).elim
      refine mem_image.mpr ⟨s(⟨x, hxS⟩, ⟨y, hyS⟩), ?_, ?_⟩
      · exact (H.mem_edgeFinset).mpr hxy
      · simp [f, Sym2.toFinset_mk_eq]
  rw [edgeCountOn, ← himage, card_image_of_injective _ hfinj]

#print axioms edgeCountOn_eq_card_edgeFinset_induce

end ForestUnimodality
