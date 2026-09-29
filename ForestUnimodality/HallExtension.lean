import ForestUnimodality.MatchingExclusion
import ForestUnimodality.ExtensionCounts

/-!
The matching-based extension row counts pairs `(J,L)` in two ways: `J` is an
independent outside r-set and `L` is an l-subset of its available vertices in
I. Fixing `L` makes ordinary independent-set extension bounds applicable.
-/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- The binomially weighted availability layers. -/
noncomputable def hallCount (G : SimpleGraph V) (I Y : Finset V) (r l : ℕ) : ℕ :=
  ∑ m ∈ range (I.card + 1), Nat.choose m l * layerCount G I Y r m

/-- Grouping outside r-sets by the number of available vertices in I. -/
theorem hallCount_eq_sum_independentLayer (G : SimpleGraph V)
    (I Y : Finset V) (r l : ℕ) :
    hallCount G I Y r l =
      ∑ J ∈ independentLayer G Y r, Nat.choose (available G I J).card l := by
  classical
  have hcover : ∀ J ∈ independentLayer G Y r,
      (available G I J).card ∈ range (I.card + 1) := by
    intro J _
    exact mem_range.mpr (Nat.lt_succ_of_le (card_le_card (available_subset G I J)))
  rw [← sum_fiberwise_of_maps_to hcover
    (fun J => Nat.choose (available G I J).card l)]
  unfold hallCount
  apply sum_congr rfl
  intro m _
  calc
    Nat.choose m l * layerCount G I Y r m =
        ∑ J ∈ (independentLayer G Y r).filter
          (fun J => (available G I J).card = m), Nat.choose m l := by
      simp [independentLayer, layerCount, filter_filter, mul_comm]
    _ = _ := by
      apply sum_congr rfl
      intro J hJ
      rw [(mem_filter.mp hJ).2]

/-- The absence of edges between two sets is symmetric. -/
theorem subset_available_comm (G : SimpleGraph V) {I Y J L : Finset V}
    (hLI : L ⊆ I) (hJY : J ⊆ Y) :
    L ⊆ available G I J ↔ J ⊆ available G Y L := by
  constructor
  · intro h j hj
    apply mem_available.mpr
    refine ⟨hJY hj, ?_⟩
    intro i hi hadj
    exact (mem_available.mp (h hi)).2 j hj hadj.symm
  · intro h i hi
    apply mem_available.mpr
    refine ⟨hLI hi, ?_⟩
    intro j hj hadj
    exact (mem_available.mp (h hj)).2 i hi hadj.symm

/-- Double counting the compatible pairs gives a sum over the fixed l-sets L.
No forest or maximality assumption is needed for this identity. -/
theorem hallCount_eq_sum_available (G : SimpleGraph V) (I Y : Finset V) (r l : ℕ) :
    hallCount G I Y r l =
      ∑ L ∈ I.powersetCard l, countIndependent G (available G Y L) r := by
  classical
  let rel : Finset V → Finset V → Prop := fun J L => L ⊆ available G I J
  have habove (J : Finset V) :
      (I.powersetCard l).bipartiteAbove rel J = (available G I J).powersetCard l := by
    ext L
    simp only [mem_bipartiteAbove, mem_powersetCard, rel]
    constructor
    · rintro ⟨⟨_, hcard⟩, hL⟩
      exact ⟨hL, hcard⟩
    · rintro ⟨hL, hcard⟩
      exact ⟨⟨hL.trans (available_subset G I J), hcard⟩, hL⟩
  have hbelow (L : Finset V) (hL : L ∈ I.powersetCard l) :
      (independentLayer G Y r).bipartiteBelow rel L =
        independentLayer G (available G Y L) r := by
    have hLI := (mem_powersetCard.mp hL).1
    ext J
    simp only [mem_bipartiteBelow, mem_independentLayer, rel]
    constructor
    · rintro ⟨⟨hJY, hJ, hcard⟩, hLJ⟩
      exact ⟨(subset_available_comm G hLI hJY).mp hLJ, hJ, hcard⟩
    · rintro ⟨hJA, hJ, hcard⟩
      have hJY := hJA.trans (available_subset G Y L)
      exact ⟨⟨hJY, hJ, hcard⟩, (subset_available_comm G hLI hJY).mpr hJA⟩
  calc
    hallCount G I Y r l =
        ∑ J ∈ independentLayer G Y r, Nat.choose (available G I J).card l :=
      hallCount_eq_sum_independentLayer G I Y r l
    _ = ∑ J ∈ independentLayer G Y r, ((I.powersetCard l).bipartiteAbove rel J).card := by
      apply sum_congr rfl
      intro J _
      rw [habove, card_powersetCard]
    _ = ∑ L ∈ I.powersetCard l, ((independentLayer G Y r).bipartiteBelow rel L).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow rel
    _ = ∑ L ∈ I.powersetCard l, countIndependent G (available G Y L) r := by
      apply sum_congr rfl
      intro L hL
      rw [hbelow L hL, card_independentLayer]

/-- Matching exclusion and one-vertex extensions give the full Hall extension
row. Natural subtraction remains valid even beyond the support. -/
theorem IsMaximumIndependentOn.hallCount_extension_bound
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) (r l : ℕ) :
    (r + 1) * hallCount G I (S \ I) (r + 1) l ≤
      ((S \ I).card - r - (l - (I.card - (S \ I).card))) *
        hallCount G I (S \ I) r l := by
  classical
  rw [hallCount_eq_sum_available, hallCount_eq_sum_available,
    mul_sum, mul_sum]
  apply sum_le_sum
  intro L hL
  obtain ⟨hLI, hLc⟩ := mem_powersetCard.mp hL
  have hexclusion := hI.available_complement_card_le_truncated hG L hLI
  have hfactor : (available G (S \ I) L).card - r ≤
      (S \ I).card - r - (l - (I.card - (S \ I).card)) := by
    rw [hLc] at hexclusion
    omega
  exact (countIndependent_extension_bound G (available G (S \ I) L) r).trans
    (Nat.mul_le_mul_right _ hfactor)

#print axioms hallCount_eq_sum_independentLayer
#print axioms hallCount_eq_sum_available
#print axioms IsMaximumIndependentOn.hallCount_extension_bound

end ForestUnimodality
