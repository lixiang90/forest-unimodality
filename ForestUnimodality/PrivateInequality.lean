import ForestUnimodality.PrivateNeighborBound
import ForestUnimodality.WeightedExtensions
import Mathlib.Tactic.Linarith

/-!
The `private(r,h)` row for actual forest layer counts. Every subtraction in
the row coefficients is in the real numbers. The interface accepts a real
threshold h; the finite-certificate row is obtained by casting its natural
threshold. The legal row range is 2 ≤ r ≤ |S \ I|.
-/

namespace ForestUnimodality

open Finset

/-- Taking positive parts preserves a lower bound on a finite sum. -/
theorem max_zero_le_sum_max_zero {A : Type*} (T : Finset A)
    (f : A → ℝ) (a : ℝ) (ha : a ≤ ∑ x ∈ T, f x) :
    max 0 a ≤ ∑ x ∈ T, max 0 (f x) := by
  apply max_le
  · exact sum_nonneg fun _ _ => le_max_left _ _
  · exact ha.trans (sum_le_sum fun _ _ => le_max_right _ _)

variable {V : Type*} [DecidableEq V]

/-- Reweighting a fixed independent-set layer by its availability statistic. -/
theorem sum_independentLayer_by_available (G : SimpleGraph V)
    (I Y : Finset V) (r : ℕ) (f : ℕ → ℝ) :
    (∑ J ∈ independentLayer G Y r, f (available G I J).card) =
      ∑ m ∈ range (I.card + 1), (layerCount G I Y r m : ℝ) * f m := by
  classical
  have hcover : ∀ J ∈ independentLayer G Y r,
      (available G I J).card ∈ range (I.card + 1) := by
    intro J _
    exact mem_range.mpr (Nat.lt_succ_of_le (card_le_card (available_subset G I J)))
  rw [← sum_fiberwise_of_maps_to hcover (fun J => f (available G I J).card)]
  apply sum_congr rfl
  intro m _
  calc
    (∑ J ∈ (independentLayer G Y r).filter
        (fun J => (available G I J).card = m), f (available G I J).card) =
        ∑ J ∈ (independentLayer G Y r).filter
          (fun J => (available G I J).card = m), f m := by
      apply sum_congr rfl
      intro J hJ
      rw [(mem_filter.mp hJ).2]
    _ = (layerCount G I Y r m : ℝ) * f m := by
      simp [independentLayer, layerCount, filter_filter, nsmul_eq_mul]

/-- The forest private-neighbor bound gives the positive-part inequality for
one outside independent set before deletion weights are double counted. -/
theorem private_weight_le_sum_erase
    (G : SimpleGraph V) (hG : G.IsAcyclic) (I J : Finset V)
    (hI : G.IsIndepSet (I : Set V)) (hJ : G.IsIndepSet (J : Set V))
    (hIJ : Disjoint I J) (r : ℕ) (hr : 2 ≤ r) (hJcard : J.card = r) (h : ℝ) :
    max 0 (((r - 1 : ℕ) : ℝ) * (available G I J).card +
      (I.card : ℝ) - (r : ℝ) + 1 - (r : ℝ) * h) ≤
      ∑ u ∈ J, max 0 (((available G I (J.erase u)).card : ℝ) - h) := by
  classical
  have hne : J.Nonempty := card_pos.mp (by omega)
  have hcovered := covered_card_le_card_sub_one_add_privateNeighbors
    G hG I J hI hJ hIJ hne
  have hmle := card_le_card (available_subset G I J)
  have hstructNat : I.card ≤ (available G I J).card + (r - 1) +
      ∑ u ∈ J, (privateNeighbors G I J u).card := by
    rw [hJcard] at hcovered
    omega
  have hstruct : (I.card : ℝ) ≤ ((available G I J).card : ℝ) +
      ((r - 1 : ℕ) : ℝ) + ((∑ u ∈ J, (privateNeighbors G I J u).card : ℕ) : ℝ) := by
    exact_mod_cast hstructNat
  have hrCast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hsum : (∑ u ∈ J, (((available G I (J.erase u)).card : ℝ) - h)) =
      (J.card : ℝ) * (((available G I J).card : ℝ) - h) +
        ((∑ u ∈ J, (privateNeighbors G I J u).card : ℕ) : ℝ) := by
    calc
      _ = ∑ u ∈ J, ((((available G I J).card : ℝ) - h) +
          ((privateNeighbors G I J u).card : ℝ)) := by
        apply sum_congr rfl
        intro u hu
        rw [card_available_erase_eq_add_privateNeighbors G I J hu, Nat.cast_add]
        ring
      _ = _ := by simp [sum_add_distrib, nsmul_eq_mul, mul_sub]
  apply max_zero_le_sum_max_zero
  rw [hsum, hJcard]
  rw [hrCast] at hstruct ⊢
  nlinarith

/-- The complete `private(r,h)` row, with real subtraction and genuine layer
counts. A natural certificate threshold is supplied as `(h : ℝ)`. -/
theorem IsMaximumIndependentOn.private_layer_inequality
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) (r : ℕ) (hr : 2 ≤ r) (hrY : r ≤ (S \ I).card) (h : ℝ) :
    (∑ m ∈ range (I.card + 1),
      max 0 (((r - 1 : ℕ) : ℝ) * (m : ℝ) + (I.card : ℝ) - (r : ℝ) + 1 -
        (r : ℝ) * h) * (layerCount G I (S \ I) r m : ℝ)) ≤
      ((S \ I).card - (r : ℝ) + 1) *
        ∑ m ∈ range (I.card + 1),
          max 0 ((m : ℝ) - h) * (layerCount G I (S \ I) (r - 1) m : ℝ) := by
  classical
  let f : Finset V → ℝ := fun J => max 0 (((available G I J).card : ℝ) - h)
  have hpoint : ∀ J ∈ independentLayer G (S \ I) r,
      max 0 (((r - 1 : ℕ) : ℝ) * (available G I J).card +
        (I.card : ℝ) - (r : ℝ) + 1 - (r : ℝ) * h) ≤ ∑ u ∈ J, f (J.erase u) := by
    intro J hJL
    obtain ⟨hJY, hJind, hJcard⟩ := mem_independentLayer.mp hJL
    have hIJ : Disjoint I J := by
      apply disjoint_left.mpr
      intro v hvI hvJ
      exact (mem_sdiff.mp (hJY hvJ)).2 hvI
    exact private_weight_le_sum_erase G hG I J hI.independent hJind hIJ r hr hJcard h
  have hweighted := weighted_independent_extension_bound G (S \ I) (r - 1) f
    (fun _ _ => le_max_left _ _)
  have hrPred : r - 1 + 1 = r := by omega
  have hfactor : (((S \ I).card - (r - 1) : ℕ) : ℝ) =
      ((S \ I).card : ℝ) - (r : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rw [hrPred, hfactor] at hweighted
  have hsum := (sum_le_sum hpoint).trans hweighted
  simp only [f] at hsum
  rw [sum_independentLayer_by_available G I (S \ I) r
      (fun m => max 0 (((r - 1 : ℕ) : ℝ) * (m : ℝ) +
        (I.card : ℝ) - (r : ℝ) + 1 - (r : ℝ) * h)),
    sum_independentLayer_by_available G I (S \ I) (r - 1)
      (fun m => max 0 ((m : ℝ) - h))] at hsum
  simpa only [mul_comm] using hsum

#print axioms max_zero_le_sum_max_zero
#print axioms sum_independentLayer_by_available
#print axioms private_weight_le_sum_erase
#print axioms IsMaximumIndependentOn.private_layer_inequality

end ForestUnimodality
