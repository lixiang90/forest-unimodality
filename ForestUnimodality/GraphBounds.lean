import ForestUnimodality.GraphCore
import ForestUnimodality.Statement

/-! Basic bounds for independent-set counts on a finite vertex subset. -/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- Enlarging the ambient vertex set preserves each independent subset. -/
theorem independentSubsets_mono (G : SimpleGraph V) {S T : Finset V}
    (hST : S ⊆ T) : independentSubsets G S ⊆ independentSubsets G T := by
  intro J hJ
  rcases mem_independentSubsets.mp hJ with ⟨hJS, hJ⟩
  exact mem_independentSubsets.mpr ⟨hJS.trans hST, hJ⟩

/-- Independent `k`-subsets are a filter of all `k`-subsets. -/
theorem countIndependent_eq_card_filter_powersetCard (G : SimpleGraph V)
    (S : Finset V) (k : ℕ) :
    countIndependent G S k = (by
      classical
      exact ((S.powersetCard k).filter fun J : Finset V =>
        G.IsIndepSet (J : Set V)).card) := by
  classical
  unfold countIndependent independentSubsets
  congr 1
  ext J
  simp [and_assoc, and_comm]

/-- The empty set is the unique independent subset of cardinality zero. -/
@[simp] theorem countIndependent_zero (G : SimpleGraph V) (S : Finset V) :
    countIndependent G S 0 = 1 := by
  classical
  rw [countIndependent_eq_card_filter_powersetCard]
  simp [Finset.filter_singleton]

/-- Every singleton is independent, so the first coefficient is the vertex count. -/
@[simp] theorem countIndependent_one (G : SimpleGraph V) (S : Finset V) :
    countIndependent G S 1 = S.card := by
  classical
  rw [countIndependent_eq_card_filter_powersetCard]
  have hFilter : ((S.powersetCard 1).filter fun J : Finset V =>
      G.IsIndepSet (J : Set V)) = S.powersetCard 1 := by
    apply Finset.filter_eq_self.mpr
    intro J hJ
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hJ).2
    simp [SimpleGraph.IsIndepSet]
  rw [hFilter, Finset.card_powersetCard, Nat.choose_one_right]

/-- Independent subsets cannot outnumber all subsets of the same cardinality. -/
theorem countIndependent_le_choose (G : SimpleGraph V) (S : Finset V) (k : ℕ) :
    countIndependent G S k ≤ Nat.choose S.card k := by
  classical
  rw [countIndependent_eq_card_filter_powersetCard, ← Finset.card_powersetCard]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Independent-set counts are monotone in the ambient vertex subset. -/
theorem countIndependent_mono (G : SimpleGraph V) {S T : Finset V}
    (hST : S ⊆ T) (k : ℕ) : countIndependent G S k ≤ countIndependent G T k := by
  classical
  apply Finset.card_le_card
  intro J hJ
  rcases Finset.mem_filter.mp hJ with ⟨hJS, hJcard⟩
  exact Finset.mem_filter.mpr ⟨independentSubsets_mono G hST hJS, hJcard⟩

/-- If every vertex in `S` is mutually nonadjacent, every subset is independent. -/
theorem countIndependent_eq_choose_of_indep (G : SimpleGraph V) (S : Finset V)
    (hS : G.IsIndepSet (S : Set V)) (k : ℕ) :
    countIndependent G S k = Nat.choose S.card k := by
  classical
  rw [countIndependent_eq_card_filter_powersetCard, ← Finset.card_powersetCard]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro J hJ
  exact hS.mono (Finset.coe_subset.mpr (Finset.mem_powersetCard.mp hJ).1)

/-- An independent subset supplies a binomial lower bound for the ambient count. -/
theorem choose_le_countIndependent_of_indep (G : SimpleGraph V) {I S : Finset V}
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) (k : ℕ) :
    Nat.choose I.card k ≤ countIndependent G S k := by
  rw [← countIndependent_eq_choose_of_indep G I hI k]
  exact countIndependent_mono G hIS k

/-- The count vanishes beyond the ambient vertex count. -/
theorem countIndependent_eq_zero_of_gt (G : SimpleGraph V) (S : Finset V)
    {k : ℕ} (hk : S.card < k) : countIndependent G S k = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [Nat.choose_eq_zero_of_lt hk] using countIndependent_le_choose G S k

/-- The finite-subset vocabulary agrees with the full target's coefficient count. -/
theorem countIndependent_univ_eq_independentCount {n : ℕ}
    (G : SimpleGraph (Fin n)) (k : ℕ) :
    countIndependent G Finset.univ k = independentCount G k := by
  classical
  unfold countIndependent independentSubsets independentCount
  congr 1
  ext J
  simp [and_comm]

end ForestUnimodality

#print axioms ForestUnimodality.countIndependent_zero
#print axioms ForestUnimodality.countIndependent_one
#print axioms ForestUnimodality.countIndependent_le_choose
#print axioms ForestUnimodality.countIndependent_mono
#print axioms ForestUnimodality.countIndependent_eq_choose_of_indep
#print axioms ForestUnimodality.choose_le_countIndependent_of_indep
#print axioms ForestUnimodality.countIndependent_eq_zero_of_gt
#print axioms ForestUnimodality.countIndependent_univ_eq_independentCount
