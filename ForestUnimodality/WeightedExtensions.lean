import ForestUnimodality.ExtensionCounts
import Mathlib.Data.Real.Basic

/-!
Weighted double counting of one-vertex deletions. Only the weights of the
independent k-sets need to be nonnegative. No acyclicity assumption is used.
-/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- All independent k-subsets of an independent (k+1)-set arise uniquely by
erasing one of its vertices. -/
theorem independentLayer_bipartiteBelow_eq_image_erase
    (G : SimpleGraph V) (S : Finset V) (k : ℕ) {J : Finset V}
    (hJ : J ∈ independentLayer G S (k + 1)) :
    (independentLayer G S k).bipartiteBelow (fun A B : Finset V => A ⊆ B) J =
      J.image J.erase := by
  classical
  obtain ⟨hJS, hJI, hJc⟩ := mem_independentLayer.mp hJ
  ext K
  constructor
  · intro hK
    obtain ⟨hKL, hKJ⟩ := mem_bipartiteBelow _ |>.mp hK
    obtain ⟨_, _, hKc⟩ := mem_independentLayer.mp hKL
    have hc : J.card = K.card + 1 := by omega
    obtain ⟨v, hvK, rfl⟩ := exists_eq_insert_iff.mpr ⟨hKJ, hc.symm⟩
    exact mem_image.mpr ⟨v, mem_insert_self _ _, by simp [hvK]⟩
  · intro hK
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hK
    apply (mem_bipartiteBelow _).mpr
    refine ⟨mem_independentLayer.mpr ⟨(erase_subset v J).trans hJS,
      hJI.mono (Finset.coe_subset.mpr (erase_subset v J)), ?_⟩, erase_subset v J⟩
    have hc := card_erase_add_one hv
    omega

/-- A fixed independent k-set has at most |S|-k one-vertex extensions. -/
theorem independentLayer_bipartiteAbove_card_le
    (G : SimpleGraph V) (S : Finset V) (k : ℕ) {K : Finset V}
    (hK : K ∈ independentLayer G S k) :
    ((independentLayer G S (k + 1)).bipartiteAbove
      (fun A B : Finset V => A ⊆ B) K).card ≤ S.card - k := by
  classical
  obtain ⟨hKS, _, hKc⟩ := mem_independentLayer.mp hK
  calc
    ((independentLayer G S (k + 1)).bipartiteAbove
        (fun A B : Finset V => A ⊆ B) K).card ≤
        ((S \ K).image fun v => insert v K).card := by
      apply card_le_card
      intro J hJ
      obtain ⟨hJL, hKJ⟩ := (mem_bipartiteAbove _).mp hJ
      obtain ⟨hJS, _, hJc⟩ := mem_independentLayer.mp hJL
      have hc : J.card = K.card + 1 := by omega
      obtain ⟨v, hvK, rfl⟩ := exists_eq_insert_iff.mpr ⟨hKJ, hc.symm⟩
      exact mem_image.mpr ⟨v, mem_sdiff.mpr ⟨hJS (mem_insert_self v K), hvK⟩, rfl⟩
    _ ≤ (S \ K).card := card_image_le
    _ = S.card - k := by rw [card_sdiff_of_subset hKS, hKc]

/-- Exact weighted double counting before the number of extensions is bounded. -/
theorem sum_erase_weights_eq_sum_extensions
    (G : SimpleGraph V) (S : Finset V) (k : ℕ) (f : Finset V → ℝ) :
    (∑ J ∈ independentLayer G S (k + 1), ∑ u ∈ J, f (J.erase u)) =
      ∑ K ∈ independentLayer G S k,
        (((independentLayer G S (k + 1)).bipartiteAbove
          (fun A B : Finset V => A ⊆ B) K).card : ℝ) * f K := by
  classical
  calc
    (∑ J ∈ independentLayer G S (k + 1), ∑ u ∈ J, f (J.erase u)) =
        ∑ J ∈ independentLayer G S (k + 1),
          ∑ K ∈ (independentLayer G S k).bipartiteBelow
            (fun A B : Finset V => A ⊆ B) J, f K := by
      apply sum_congr rfl
      intro J hJ
      rw [independentLayer_bipartiteBelow_eq_image_erase G S k hJ,
        sum_image J.erase_injOn]
    _ = ∑ K ∈ independentLayer G S k,
        ∑ J ∈ (independentLayer G S (k + 1)).bipartiteAbove
          (fun A B : Finset V => A ⊆ B) K, f K :=
      (sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow
        (fun A B : Finset V => A ⊆ B) (fun K _ => f K)).symm
    _ = _ := by simp [nsmul_eq_mul]

/-- The sum of deletion weights is bounded by |S|-k times the total weight of
the independent k-layer. Nonnegativity is needed only on that layer. -/
theorem weighted_independent_extension_bound
    (G : SimpleGraph V) (S : Finset V) (k : ℕ) (f : Finset V → ℝ)
    (hf : ∀ K ∈ independentLayer G S k, 0 ≤ f K) :
    (∑ J ∈ independentLayer G S (k + 1), ∑ u ∈ J, f (J.erase u)) ≤
      ((S.card - k : ℕ) : ℝ) * ∑ K ∈ independentLayer G S k, f K := by
  classical
  rw [sum_erase_weights_eq_sum_extensions, mul_sum]
  apply sum_le_sum
  intro K hK
  apply mul_le_mul_of_nonneg_right _ (hf K hK)
  exact_mod_cast independentLayer_bipartiteAbove_card_le G S k hK

#print axioms independentLayer_bipartiteBelow_eq_image_erase
#print axioms independentLayer_bipartiteAbove_card_le
#print axioms sum_erase_weights_eq_sum_extensions
#print axioms weighted_independent_extension_bound

end ForestUnimodality
