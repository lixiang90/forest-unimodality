import Mathlib.Data.List.Sort
import Mathlib.Data.List.Nodup

/-! Derive distinctness from adjacent comparisons of a natural-number rank. -/
namespace ForestUnimodality

theorem nodup_of_adjacent_nat_rank {A : Type*} (rank : A → ℕ) {xs : List A}
    (h : (xs.map rank).IsChain (· < ·)) : xs.Nodup := by
  exact List.Nodup.of_map rank h.sortedLT.nodup

#print axioms nodup_of_adjacent_nat_rank
end ForestUnimodality
