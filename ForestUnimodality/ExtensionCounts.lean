import ForestUnimodality.GraphBounds
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! Double counting one-vertex extensions of independent sets. -/

namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

noncomputable def independentLayer (G : SimpleGraph V) (S : Finset V) (k : ℕ) :
    Finset (Finset V) := by
  classical
  exact (independentSubsets G S).filter fun J => J.card = k

@[simp] theorem mem_independentLayer {G : SimpleGraph V} {S J : Finset V} {k : ℕ} :
    J ∈ independentLayer G S k ↔ J ⊆ S ∧ G.IsIndepSet (J : Set V) ∧ J.card = k := by
  classical
  simp [independentLayer, mem_independentSubsets, and_assoc]

@[simp] theorem card_independentLayer (G : SimpleGraph V) (S : Finset V) (k : ℕ) :
    (independentLayer G S k).card = countIndependent G S k := rfl

/-- Deleting any one vertex of an independent (k+1)-set gives distinct
independent k-sets. Each independent k-set has at most |S|-k extensions. -/
theorem countIndependent_extension_bound (G : SimpleGraph V) (S : Finset V) (k : ℕ) :
    (k + 1) * countIndependent G S (k + 1) ≤
      (S.card - k) * countIndependent G S k := by
  classical
  have h := Finset.card_mul_le_card_mul' (s := independentLayer G S k)
    (t := independentLayer G S (k + 1)) (fun A B : Finset V => A ⊆ B)
    (n := k + 1) (m := S.card - k) ?_ ?_
  · simpa only [card_independentLayer, mul_comm] using h
  · intro J hJ
    obtain ⟨hJS, hJI, hJc⟩ := mem_independentLayer.mp hJ
    rw [← hJc, ← Finset.card_image_of_injOn J.erase_injOn]
    apply Finset.card_le_card
    intro K hK
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hK
    apply (Finset.mem_bipartiteBelow _).mpr
    refine ⟨mem_independentLayer.mpr ⟨(erase_subset v J).trans hJS,
      hJI.mono (Finset.coe_subset.mpr (erase_subset v J)), ?_⟩, erase_subset v J⟩
    have hc := card_erase_add_one hv
    omega
  · intro K hK
    obtain ⟨hKS, hKI, hKc⟩ := mem_independentLayer.mp hK
    calc
      ((independentLayer G S (k + 1)).bipartiteAbove
          (fun A B : Finset V => A ⊆ B) K).card ≤
          ((S \ K).image fun v => insert v K).card := by
        apply Finset.card_le_card
        intro J hJ
        obtain ⟨hJL, hKJ⟩ := (mem_bipartiteAbove _).mp hJ
        obtain ⟨hJS, hJI, hJc⟩ := mem_independentLayer.mp hJL
        have hc : J.card = K.card + 1 := by omega
        obtain ⟨v, hvK, rfl⟩ := Finset.exists_eq_insert_iff.mpr ⟨hKJ, hc.symm⟩
        exact mem_image.mpr ⟨v, mem_sdiff.mpr ⟨hJS (mem_insert_self v K), hvK⟩, rfl⟩
      _ ≤ (S \ K).card := card_image_le
      _ = S.card - k := by rw [card_sdiff_of_subset hKS, hKc]

/-- Every graph's independent-set counts are nonincreasing from the middle
of the vertex range onward. -/
theorem countIndependent_succ_le_of_middle (G : SimpleGraph V) (S : Finset V)
    (k : ℕ) (hmiddle : S.card ≤ 2 * k + 1) :
    countIndependent G S (k + 1) ≤ countIndependent G S k := by
  have h := countIndependent_extension_bound G S k
  have hfactor : S.card - k ≤ k + 1 := by omega
  have hb := h.trans (Nat.mul_le_mul_right (countIndependent G S k) hfactor)
  exact Nat.le_of_mul_le_mul_left hb (by omega)

#print axioms countIndependent_extension_bound
#print axioms countIndependent_succ_le_of_middle
end ForestUnimodality
