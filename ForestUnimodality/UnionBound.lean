import ForestUnimodality.PrivateInequality

/-! Coverage union bounds for the actual independent-set layers. These bounds
hold for every simple graph and arbitrary finite sets I and Y. -/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- The vertices covered by J are the union of its singleton coverages. -/
theorem covered_eq_biUnion_singleton (G : SimpleGraph V) (I J : Finset V) :
    I \ available G I J = J.biUnion (fun u => I \ available G I {u}) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨hxI, hxnot⟩ := mem_sdiff.mp hx
    have hex : ∃ u ∈ J, G.Adj x u := by
      by_contra h
      push Not at h
      exact hxnot (mem_available.mpr ⟨hxI, h⟩)
    obtain ⟨u, hu, hxu⟩ := hex
    apply mem_biUnion.mpr
    refine ⟨u, hu, mem_sdiff.mpr ⟨hxI, ?_⟩⟩
    intro hxa
    exact (mem_available.mp hxa).2 u (mem_singleton_self u) hxu
  · intro hx
    obtain ⟨u, hu, hxu⟩ := mem_biUnion.mp hx
    obtain ⟨hxI, hxnot⟩ := mem_sdiff.mp hxu
    apply mem_sdiff.mpr
    refine ⟨hxI, ?_⟩
    intro hxa
    apply hxnot
    apply mem_available.mpr
    refine ⟨hxI, ?_⟩
    intro v hv
    have hvu := mem_singleton.mp hv
    subst v
    exact (mem_available.mp hxa).2 u hu

/-- The elementary coverage union bound before summing over a layer. -/
theorem covered_card_le_sum_singleton (G : SimpleGraph V) (I J : Finset V) :
    I.card - (available G I J).card ≤
      ∑ u ∈ J, (I.card - (available G I {u}).card) := by
  classical
  have h := card_biUnion_le (s := J) (t := fun u => I \ available G I {u})
  rw [← covered_eq_biUnion_singleton G I J] at h
  simpa only [card_sdiff_of_subset (available_subset G I _)] using h

/-- An element lies in at most the unrestricted number of r-subsets. -/
theorem card_independentLayer_containing_le (G : SimpleGraph V) (Y : Finset V)
    (r : ℕ) (hr : 1 ≤ r) {u : V} (hu : u ∈ Y) :
    ((independentLayer G Y r).filter fun J => u ∈ J).card ≤
      (Y.card - 1).choose (r - 1) := by
  classical
  calc
    _ ≤ ((Y.powersetCard r).filter ({u} ⊆ ·)).card := by
      apply card_le_card
      intro J hJ
      obtain ⟨hJL, huJ⟩ := mem_filter.mp hJ
      obtain ⟨hJY, _, hJcard⟩ := mem_independentLayer.mp hJL
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hJY, hJcard⟩,
        singleton_subset_iff.mpr huJ⟩
    _ = _ := by
      simpa using card_filter_powersetCard_subset {u} Y r
        (singleton_subset_iff.mpr hu) (by simpa using hr)

/-- Weighted membership counting for an independent-set layer. -/
theorem sum_independentLayer_vertex_weights_le (G : SimpleGraph V)
    (Y : Finset V) (r : ℕ) (hr : 1 ≤ r) (f : V → ℕ) :
    (∑ J ∈ independentLayer G Y r, ∑ u ∈ J, f u) ≤
      (Y.card - 1).choose (r - 1) * ∑ u ∈ Y, f u := by
  classical
  calc
    _ = ∑ J ∈ independentLayer G Y r, ∑ u ∈ Y, if u ∈ J then f u else 0 := by
      apply sum_congr rfl
      intro J hJ
      rw [← sum_filter]
      have hfilter : Y.filter (· ∈ J) = J := by
        ext u
        simp only [mem_filter]
        exact and_iff_right_of_imp (fun hu => (mem_independentLayer.mp hJ).1 hu)
      rw [hfilter]
    _ = ∑ u ∈ Y, ∑ J ∈ independentLayer G Y r, if u ∈ J then f u else 0 :=
      sum_comm
    _ = ∑ u ∈ Y, ((independentLayer G Y r).filter fun J => u ∈ J).card * f u := by
      apply sum_congr rfl
      intro u _
      rw [← sum_filter]
      simp
    _ ≤ ∑ u ∈ Y, (Y.card - 1).choose (r - 1) * f u := by
      apply sum_le_sum
      intro u hu
      exact Nat.mul_le_mul_right (f u) (card_independentLayer_containing_le G Y r hr hu)
    _ = _ := (mul_sum _ _ _).symm

/-- The independent one-layer is exactly the singleton image of Y. -/
theorem independentLayer_one_eq_singleton_image (G : SimpleGraph V) (Y : Finset V) :
    independentLayer G Y 1 = Y.image (fun u => {u}) := by
  classical
  ext J
  constructor
  · intro hJ
    obtain ⟨hJY, _, hJcard⟩ := mem_independentLayer.mp hJ
    obtain ⟨u, rfl⟩ := card_eq_one.mp hJcard
    exact mem_image.mpr ⟨u, hJY (mem_singleton_self u), rfl⟩
  · intro hJ
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hJ
    apply mem_independentLayer.mpr
    refine ⟨singleton_subset_iff.mpr hu, ?_, card_singleton u⟩
    simp [SimpleGraph.IsIndepSet, Set.Pairwise]

/-- Reweighting a layer over the natural numbers retains all possible m. -/
theorem sum_independentLayer_by_available_nat (G : SimpleGraph V)
    (I Y : Finset V) (r : ℕ) (f : ℕ → ℕ) :
    (∑ J ∈ independentLayer G Y r, f (available G I J).card) =
      ∑ m ∈ range (I.card + 1), layerCount G I Y r m * f m := by
  classical
  have hcover : ∀ J ∈ independentLayer G Y r,
      (available G I J).card ∈ range (I.card + 1) := by
    intro J _
    exact mem_range.mpr (Nat.lt_succ_of_le (card_le_card (available_subset G I J)))
  rw [← sum_fiberwise_of_maps_to hcover (fun J => f (available G I J).card)]
  apply sum_congr rfl
  intro m _
  calc
    _ = ∑ J ∈ (independentLayer G Y r).filter
        (fun J => (available G I J).card = m), f m := by
      apply sum_congr rfl
      intro J hJ
      rw [(mem_filter.mp hJ).2]
    _ = _ := by simp [independentLayer, layerCount, filter_filter]

/-- Natural-number form of the coverage union row, valid already for r ≥ 1. -/
theorem coverage_union_layer_nat (G : SimpleGraph V) (I Y : Finset V)
    (r : ℕ) (hr : 1 ≤ r) :
    (∑ m ∈ range (I.card + 1), (I.card - m) * layerCount G I Y r m) ≤
      (Y.card - 1).choose (r - 1) *
        ∑ m ∈ range (I.card + 1), (I.card - m) * layerCount G I Y 1 m := by
  classical
  have hpoint := sum_le_sum (s := independentLayer G Y r)
    (fun J _ => covered_card_le_sum_singleton G I J)
  have hcount := sum_independentLayer_vertex_weights_le G Y r hr
    (fun u => I.card - (available G I {u}).card)
  have hsum := hpoint.trans hcount
  have hone : (∑ u ∈ Y, (I.card - (available G I {u}).card)) =
      ∑ J ∈ independentLayer G Y 1, (I.card - (available G I J).card) := by
    rw [independentLayer_one_eq_singleton_image, sum_image]
    intro u _ v _ huv
    exact singleton_injective huv
  rw [hone, sum_independentLayer_by_available_nat,
    sum_independentLayer_by_available_nat] at hsum
  simpa only [Nat.mul_comm] using hsum

/-- Real linear form of the finite-certificate coverage union row. -/
theorem coverage_union_layer (G : SimpleGraph V) (I Y : Finset V)
    (r : ℕ) (hr : 1 ≤ r) :
    (∑ m ∈ range (I.card + 1), ((I.card : ℝ) - (m : ℝ)) *
        (layerCount G I Y r m : ℝ)) ≤
      ((Y.card - 1).choose (r - 1) : ℝ) *
        ∑ m ∈ range (I.card + 1), ((I.card : ℝ) - (m : ℝ)) *
          (layerCount G I Y 1 m : ℝ) := by
  have hnat := coverage_union_layer_nat G I Y r hr
  have hcast : (∑ m ∈ range (I.card + 1), ((I.card - m : ℕ) : ℝ) *
      (layerCount G I Y r m : ℝ)) ≤
      ((Y.card - 1).choose (r - 1) : ℝ) *
        ∑ m ∈ range (I.card + 1), ((I.card - m : ℕ) : ℝ) *
          (layerCount G I Y 1 m : ℝ) := by exact_mod_cast hnat
  have hrewrite : ∀ k : ℕ,
      (∑ m ∈ range (I.card + 1), ((I.card - m : ℕ) : ℝ) *
        (layerCount G I Y k m : ℝ)) =
      ∑ m ∈ range (I.card + 1), ((I.card : ℝ) - (m : ℝ)) *
        (layerCount G I Y k m : ℝ) := by
    intro k
    apply sum_congr rfl
    intro m hm
    rw [Nat.cast_sub (by have := mem_range.mp hm; omega)]
  simpa only [hrewrite] using hcast

#print axioms covered_eq_biUnion_singleton
#print axioms covered_card_le_sum_singleton
#print axioms card_independentLayer_containing_le
#print axioms sum_independentLayer_vertex_weights_le
#print axioms coverage_union_layer_nat
#print axioms coverage_union_layer

end ForestUnimodality
