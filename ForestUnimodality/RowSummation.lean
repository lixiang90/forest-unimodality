import ForestUnimodality.RowSemantics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Common exact summation bridges from executable rows to actual graph counts. -/
namespace ForestUnimodality
namespace FiniteRows
open Finset
variable {V : Type*} [DecidableEq V]

/-- Recover a positive rectangular layer from the common triangular domain. -/
theorem _root_.ForestUnimodality.IsMaximumIndependentOn.sum_indicator_layer
    {G : SimpleGraph V} {S I : Finset V}
    (hI : ForestUnimodality.IsMaximumIndependentOn G S I)
    (r : ℕ) (hr : 1 ≤ r) (hrv : r ≤ (S \ I).card) (f : ℕ → ℝ) :
    (∑ p ∈ triangularIndices I.card (S \ I).card,
      (indicator p.1 r : ℝ) * f p.2 * (layerCount G I (S \ I) p.1 p.2 : ℝ)) =
      ∑ m ∈ range (I.card + 1), f m * (layerCount G I (S \ I) r m : ℝ) := by
  have h := hI.sum_layers_eq_zero_add_triangular
    (fun j m => (indicator j r : ℝ) * f m)
  have hrmem : r ∈ range ((S \ I).card + 1) := mem_range.mpr (by omega)
  have hrect : (∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
      (layerCount G I (S \ I) j m : ℝ) * ((indicator j r : ℝ) * f m)) =
      ∑ m ∈ range (I.card + 1), (layerCount G I (S \ I) r m : ℝ) * f m := by
    simp [indicator, mul_ite, ite_mul, hrmem]
  rw [hrect] at h
  have hrne : 0 ≠ r := by omega
  simp only [indicator, hrne, ↓reduceIte, Int.cast_zero, zero_mul, zero_add] at h
  simpa only [indicator, mul_comm, mul_left_comm, mul_assoc] using h.symm

/-- There is no zero-layer variable in the triangular certificate domain. -/
theorem sum_indicator_zero (G : SimpleGraph V) (I Y : Finset V) (f : ℕ → ℝ) :
    (∑ p ∈ triangularIndices I.card Y.card,
      (indicator p.1 0 : ℝ) * f p.2 * (layerCount G I Y p.1 p.2 : ℝ)) = 0 := by
  apply sum_eq_zero
  intro p hp
  have hpos := (mem_triangularIndices.mp hp).1
  have hne : p.1 ≠ 0 := by omega
  simp [indicator, hne]

/-- The omitted actual zero layer contributes one explicit constant. -/
theorem sum_layer_zero (G : SimpleGraph V) (I Y : Finset V) (f : ℕ → ℝ) :
    (∑ m ∈ range (I.card + 1), f m * (layerCount G I Y 0 m : ℝ)) = f I.card := by
  classical
  simp [layerCount_zero, mul_ite]

theorem _root_.ForestUnimodality.IsMaximumIndependentOn.sum_indicator_count
    {G : SimpleGraph V} {S I : Finset V}
    (hI : ForestUnimodality.IsMaximumIndependentOn G S I)
    (r : ℕ) (hr : 1 ≤ r) (hrv : r ≤ (S \ I).card) :
    (∑ p ∈ triangularIndices I.card (S \ I).card,
      (indicator p.1 r : ℝ) * (layerCount G I (S \ I) p.1 p.2 : ℝ)) =
      (countIndependent G (S \ I) r : ℝ) := by
  have h := hI.sum_indicator_layer r hr hrv (fun _ => 1)
  simp only [mul_one, one_mul] at h
  rw [h]
  exact_mod_cast sum_layerCount_eq_countIndependent G I (S \ I) r

/-- The second guarded index is exactly the preceding coefficient for k≥1. -/
theorem _root_.ForestUnimodality.IsMaximumIndependentOn.rowValue_eq_two_layers
    {G : SimpleGraph V} {S I : Finset V}
    (hI : ForestUnimodality.IsMaximumIndependentOn G S I)
    (row : Row) (r s : ℕ) (hr : 1 ≤ r) (hrv : r ≤ (S \ I).card)
    (hs : 1 ≤ s) (hsv : s ≤ (S \ I).card) (f g : ℕ → ℝ)
    (hc : ∀ p ∈ triangularIndices I.card (S \ I).card,
      (coeff S.card I.card row p : ℝ) =
        (indicator p.1 r : ℝ) * f p.2 - (indicator p.1 s : ℝ) * g p.2) :
    rowValue G S I row =
      (∑ m ∈ range (I.card + 1), f m * (layerCount G I (S \ I) r m : ℝ)) -
        ∑ m ∈ range (I.card + 1), g m * (layerCount G I (S \ I) s m : ℝ) := by
  unfold rowValue
  calc
    _ = ∑ p ∈ triangularIndices I.card (S \ I).card,
        ((indicator p.1 r : ℝ) * f p.2 - (indicator p.1 s : ℝ) * g p.2) *
          (layerCount G I (S \ I) p.1 p.2 : ℝ) := by
      apply sum_congr rfl
      intro p hp
      rw [hc p hp]
    _ = _ := by
      simp only [sub_mul, sum_sub_distrib]
      rw [hI.sum_indicator_layer r hr hrv, hI.sum_indicator_layer s hs hsv]

/-- The second guarded index is exactly the preceding coefficient for k≥1. -/
theorem differenceCoeff_cast (m j k : ℕ) (hk : 1 ≤ k) :
    (differenceCoeff m j k : ℝ) =
      (shiftedChoose m j k : ℝ) - (shiftedChoose m j (k - 1) : ℝ) := by
  cases k with
  | zero => omega
  | succ k => simp [differenceCoeff, shiftedChoose_succ_succ]

/-- Exact semantic interpretation of the source difference row. -/
theorem _root_.ForestUnimodality.IsMaximumIndependentOn.delta_eq_differenceCoeff_add_rowValue
    {G : SimpleGraph V} {S I : Finset V}
    (hI : ForestUnimodality.IsMaximumIndependentOn G S I) (k : ℕ) (hk : 1 ≤ k) :
    (countIndependent G S k : ℝ) - (countIndependent G S (k - 1) : ℝ) =
      (differenceCoeff I.card 0 k : ℝ) + rowValue G S I (.assumptionRow k) := by
  rw [hI.countIndependent_delta_eq_triangular k hk]
  rw [differenceCoeff_cast I.card 0 k hk, shiftedChoose_zero_shift,
    shiftedChoose_zero_shift]
  congr 1
  unfold rowValue
  apply sum_congr rfl
  intro p _
  simp only [coeff, differenceCoeff_cast _ _ k hk]
  ring

/-- A conditional assumption row means precisely that the actual source
difference is nonpositive. It is not asserted unconditionally. -/
theorem _root_.ForestUnimodality.IsMaximumIndependentOn.assumptionRow_iff
    {G : SimpleGraph V} {S I : Finset V}
    (hI : ForestUnimodality.IsMaximumIndependentOn G S I) (k : ℕ) (hk : 1 ≤ k) :
    RowHolds G S I (.assumptionRow k) ↔
      (countIndependent G S k : ℝ) - (countIndependent G S (k - 1) : ℝ) ≤ 0 := by
  have h := hI.delta_eq_differenceCoeff_add_rowValue k hk
  unfold RowHolds
  simp only [rhs, Int.cast_neg]
  constructor <;> intro hh <;> linarith

#print axioms IsMaximumIndependentOn.sum_indicator_layer
#print axioms sum_indicator_zero
#print axioms sum_layer_zero
#print axioms IsMaximumIndependentOn.sum_indicator_count
#print axioms differenceCoeff_cast
#print axioms IsMaximumIndependentOn.delta_eq_differenceCoeff_add_rowValue
#print axioms IsMaximumIndependentOn.assumptionRow_iff
end FiniteRows
end ForestUnimodality
