import ForestUnimodality.ExtensionCounts
import ForestUnimodality.SmallIndependence
import ForestUnimodality.PathLowerBound

/-! Complete small-order cases, with one undetermined step at the peak. -/

namespace ForestUnimodality

/-- If only one step can have either sign, one of its endpoints is a peak. -/
theorem weaklyUnimodal_of_one_unknown_step (f : ℕ → ℕ) (p : ℕ)
    (hbefore : ∀ k, k < p → f k ≤ f (k + 1))
    (hafter : ∀ k, p + 1 ≤ k → f (k + 1) ≤ f k) : WeaklyUnimodal f := by
  by_cases hstep : f p ≤ f (p + 1)
  · refine ⟨p + 1, ?_, hafter⟩
    intro k hk
    by_cases hkp : k = p
    · simpa [hkp] using hstep
    · exact hbefore k (by omega)
  · refine ⟨p, hbefore, ?_⟩
    intro k hk
    by_cases hkp : k = p
    · simpa [hkp] using le_of_lt (lt_of_not_ge hstep)
    · exact hafter k (by omega)

variable {V : Type*} [DecidableEq V]

/-- All graphs on at most five vertices have unimodal independence counts. -/
theorem countIndependent_unimodal_of_card_le_five (G : SimpleGraph V)
    (S : Finset V) (hS : S.card ≤ 5) : WeaklyUnimodal (countIndependent G S) := by
  by_cases hEmpty : S = ∅
  · subst S
    exact countIndependent_empty_unimodal G
  have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hEmpty)
  apply weaklyUnimodal_of_one_unknown_step _ 1
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simpa using hpos
  · intro k hk
    exact countIndependent_succ_le_of_middle G S k (by omega)

/-- The path lower bound supplies the additional increasing step needed for
forests on six or seven vertices; the remaining middle step chooses the peak. -/
theorem countIndependent_unimodal_of_isAcyclic_card_le_seven
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (hS : S.card ≤ 7) : WeaklyUnimodal (countIndependent G S) := by
  by_cases hsmall : S.card ≤ 5
  · exact countIndependent_unimodal_of_card_le_five G S hsmall
  have hsize : S.card = 6 ∨ S.card = 7 := by omega
  have h12 : countIndependent G S 1 ≤ countIndependent G S 2 := by
    have hb := choose_path_le_countIndependent G hG S 2
    rw [countIndependent_one]
    rcases hsize with h6 | h7
    · norm_num [h6, Nat.choose] at hb ⊢
      omega
    · norm_num [h7, Nat.choose] at hb ⊢
      omega
  apply weaklyUnimodal_of_one_unknown_step _ 2
  · intro k hk
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · simp only [Nat.zero_add, countIndependent_zero, countIndependent_one]
      omega
    · exact h12
  · intro k hk
    exact countIndependent_succ_le_of_middle G S k (by omega)

/-- The bounded forest theorem in the exact count vocabulary of CompleteTarget. -/
theorem independentCount_unimodal_of_isAcyclic_card_le_seven {n : ℕ}
    (G : SimpleGraph (Fin n)) (hG : G.IsAcyclic) (hn : n ≤ 7) :
    WeaklyUnimodal (independentCount G) := by
  have h := countIndependent_unimodal_of_isAcyclic_card_le_seven G hG Finset.univ
    (by simpa using hn)
  simpa only [WeaklyUnimodal, countIndependent_univ_eq_independentCount] using h

#print axioms weaklyUnimodal_of_one_unknown_step
#print axioms countIndependent_unimodal_of_card_le_five
#print axioms countIndependent_unimodal_of_isAcyclic_card_le_seven
#print axioms independentCount_unimodal_of_isAcyclic_card_le_seven
end ForestUnimodality
