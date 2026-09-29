import ForestUnimodality.IndependentSplit
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Finite layer counts for the independently proved independent-set decomposition.
The two indices record the size of the outside independent set and the number
of vertices in I still available. All grouping is proved using finite fibers.
-/

namespace ForestUnimodality

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- Number of outside independent sets with size j and exactly m available
vertices in I. The definition imposes no independence assumption on I. -/
noncomputable def layerCount (G : SimpleGraph V) (I Y : Finset V) (j m : ℕ) : ℕ :=
  ((independentSubsets G Y).filter fun J =>
    J.card = j ∧ (available G I J).card = m).card

@[simp] theorem available_empty (G : SimpleGraph V) (I : Finset V) :
    available G I ∅ = I := by
  classical
  ext v
  simp

/-- The empty outside set is the unique member of layer zero. -/
theorem layerCount_zero (G : SimpleGraph V) (I Y : Finset V) (m : ℕ) :
    layerCount G I Y 0 m = if I.card = m then 1 else 0 := by
  classical
  have hfilter : ((independentSubsets G Y).filter fun J =>
      J.card = 0 ∧ (available G I J).card = m) =
      if I.card = m then {∅} else ∅ := by
    ext J
    by_cases hJ : J = ∅
    · subst J
      by_cases hm : I.card = m <;>
        simp [hm, mem_independentSubsets, SimpleGraph.IsIndepSet, Set.Pairwise]
    · by_cases hm : I.card = m <;> simp [hJ, hm]
  unfold layerCount
  rw [hfilter]
  split <;> simp

@[simp] theorem layerCount_zero_card (G : SimpleGraph V) (I Y : Finset V) :
    layerCount G I Y 0 I.card = 1 := by
  simp [layerCount_zero]

theorem layerCount_zero_of_ne (G : SimpleGraph V) (I Y : Finset V) {m : ℕ}
    (hm : m ≠ I.card) : layerCount G I Y 0 m = 0 := by
  simp [layerCount_zero, Ne.symm hm]

/-- Summing the availability layers gives the actual independent j-set count. -/
theorem sum_layerCount_eq_countIndependent
    (G : SimpleGraph V) (I Y : Finset V) (j : ℕ) :
    (∑ m ∈ range (I.card + 1), layerCount G I Y j m) = countIndependent G Y j := by
  classical
  have hcover : ∀ J ∈ (independentSubsets G Y).filter (fun J => J.card = j),
      (available G I J).card ∈ range (I.card + 1) := by
    intro J _
    exact mem_range.mpr (Nat.lt_succ_of_le (card_le_card (available_subset G I J)))
  have hf := sum_fiberwise_of_maps_to hcover (fun _ => (1 : ℕ))
  simpa [layerCount, countIndependent, filter_filter] using hf

/-- A general finite-fiber identity, usable with any semiring-valued function
of the two statistics. -/
theorem sum_independentSubsets_by_layers {R : Type*} [CommSemiring R]
    (G : SimpleGraph V) (I Y : Finset V) (F : ℕ → ℕ → R) :
    (∑ J ∈ independentSubsets G Y, F J.card (available G I J).card) =
      ∑ j ∈ range (Y.card + 1), ∑ m ∈ range (I.card + 1),
        (layerCount G I Y j m : R) * F j m := by
  classical
  have hcover : ∀ J ∈ independentSubsets G Y,
      (J.card, (available G I J).card) ∈
        (range (Y.card + 1)) ×ˢ (range (I.card + 1)) := by
    intro J hJ
    apply mem_product.mpr
    exact ⟨mem_range.mpr (Nat.lt_succ_of_le
      (card_le_card (mem_independentSubsets.mp hJ).1)),
      mem_range.mpr (Nat.lt_succ_of_le (card_le_card (available_subset G I J)))⟩
  rw [← sum_fiberwise_of_maps_to hcover
    (fun J => F J.card (available G I J).card), sum_product]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro m _
  simp only [Prod.mk.injEq]
  calc
    (∑ J ∈ (independentSubsets G Y).filter
        (fun J => J.card = j ∧ (available G I J).card = m),
        F J.card (available G I J).card) =
      ∑ J ∈ (independentSubsets G Y).filter
        (fun J => J.card = j ∧ (available G I J).card = m), F j m := by
      apply sum_congr rfl
      intro J hJ
      obtain ⟨hj, hm⟩ := (mem_filter.mp hJ).2
      rw [hj, hm]
    _ = (layerCount G I Y j m : R) * F j m := by
      simp [layerCount, nsmul_eq_mul]

/-- The full generating-function decomposition grouped by both layer indices. -/
theorem partitionFunction_layer_decomposition {R : Type*} [CommSemiring R]
    (G : SimpleGraph V) (S I : Finset V) (hIS : I ⊆ S)
    (hI : G.IsIndepSet (I : Set V)) (z : R) :
    partitionFunction G S z =
      ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
        (layerCount G I (S \ I) j m : R) * z^j * (1 + z)^m := by
  rw [partitionFunction_decomposition S I hIS hI z,
    sum_independentSubsets_by_layers G I (S \ I)
      (fun j m => z^j * (1 + z)^m)]
  simp only [mul_assoc]

#print axioms sum_independentSubsets_by_layers
#print axioms partitionFunction_layer_decomposition
#print axioms layerCount_zero
#print axioms sum_layerCount_eq_countIndependent

end ForestUnimodality
