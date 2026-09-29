import ForestUnimodality.ExtensionCounts
import ForestUnimodality.MaximumIndependent

/-! Arbitrarily large edgeless induced graphs and the complementary parameter bound. -/

namespace ForestUnimodality
variable {V : Type*} [DecidableEq V]

/-- For an independent ambient vertex set the sequence is binomial, with
peak at floor(|S|/2). This includes the empty ambient set. -/
theorem countIndependent_unimodal_of_indep (G : SimpleGraph V) (S : Finset V)
    (hS : G.IsIndepSet (S : Set V)) : WeaklyUnimodal (countIndependent G S) := by
  refine ⟨S.card / 2, ?_, ?_⟩
  · intro k hk
    rw [countIndependent_eq_choose_of_indep G S hS k,
      countIndependent_eq_choose_of_indep G S hS (k + 1)]
    exact Nat.choose_le_succ_of_lt_half_left hk
  · intro k hk
    exact countIndependent_succ_le_of_middle G S k (by omega)

/-- If the ambient induced graph has an edge, a maximum independent subset
has strictly fewer vertices than the ambient set. -/
theorem IsMaximumIndependentOn.card_lt_of_not_indep
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hS : ¬ G.IsIndepSet (S : Set V)) : I.card < S.card := by
  have hle := Finset.card_le_card hI.subset
  by_contra hnot
  have heq : I = S := Finset.eq_of_subset_of_card_le hI.subset (by omega)
  exact hS (heq ▸ hI.independent)

#print axioms countIndependent_unimodal_of_indep
#print axioms IsMaximumIndependentOn.card_lt_of_not_indep
end ForestUnimodality
