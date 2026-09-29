import ForestUnimodality.RowSummation
import ForestUnimodality.PathLowerBound
import ForestUnimodality.HallExtension
import ForestUnimodality.UnionBound

/-! Soundness of six executable primitive rows for actual graph layer counts. -/
namespace ForestUnimodality
namespace FiniteRows
open Finset
variable {V : Type*} [DecidableEq V]

theorem rowHolds_count {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (r : ℕ)
    (hr : 1 ≤ r) (hrv : r ≤ (S \ I).card) : RowHolds G S I (.count r) := by
  unfold RowHolds rowValue
  simp only [coeff, rhs, Int.cast_natCast]
  rw [hI.sum_indicator_count r hr hrv, ← card_sdiff_of_subset hI.subset]
  exact_mod_cast countIndependent_le_choose G (S \ I) r

theorem rowValue_path_eq {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (r : ℕ) :
    rowValue G S I (.path r) = (I.card.choose r : ℝ) - (countIndependent G S r : ℝ) := by
  have h := hI.countIndependent_cast_eq_triangular (R := ℝ) r
  unfold rowValue
  simp only [coeff, Int.cast_neg, Int.cast_natCast, neg_mul, sum_neg_distrib]
  have heq : (∑ p ∈ triangularIndices I.card (S \ I).card,
      (shiftedChoose p.2 p.1 r : ℝ) * (layerCount G I (S \ I) p.1 p.2 : ℝ)) =
      ∑ p ∈ triangularIndices I.card (S \ I).card,
        (layerCount G I (S \ I) p.1 p.2 : ℝ) * (shiftedChoose p.2 p.1 r : ℝ) := by
    apply sum_congr rfl
    intro p _
    ring
  rw [heq]
  linarith

theorem rowHolds_path {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic) (r : ℕ) :
    RowHolds G S I (.path r) := by
  unfold RowHolds
  rw [rowValue_path_eq hI r]
  simp only [rhs, Int.cast_sub, Int.cast_natCast]
  have h : ((S.card + 1 - r).choose r : ℝ) ≤ (countIndependent G S r : ℝ) := by
    exact_mod_cast choose_path_le_countIndependent G hG S r
  linarith

theorem rowHolds_private {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic)
    (r h : ℕ) (hr : 2 ≤ r) (hrv : r ≤ (S \ I).card) :
    RowHolds G S I (.privateRow r h) := by
  classical
  let f : ℕ → ℝ := fun m => max 0
    (((r : ℝ) - 1) * (m : ℝ) + (I.card : ℝ) - (r : ℝ) + 1 - (r : ℝ) * h)
  let g : ℕ → ℝ := fun m =>
    (((S \ I).card - (r - 1) : ℕ) : ℝ) * max 0 ((m : ℝ) - h)
  have hvalue := hI.rowValue_eq_two_layers (.privateRow r h) r (r - 1)
    (by omega) hrv (by omega) (by omega) f g (by
      intro p _
      simp only [coeff, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
        Int.cast_add, Int.cast_one, Int.cast_zero, Int.cast_max]
      rw [← card_sdiff_of_subset hI.subset]
      dsimp [f, g]
      ring)
  have hbound := hI.private_layer_inequality hG r hr hrv (h : ℝ)
  have hfactor : (((S \ I).card - (r - 1) : ℕ) : ℝ) =
      ((S \ I).card : ℝ) - (r : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    ring
  have hrpred : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  unfold RowHolds
  rw [hvalue]
  simp only [rhs, Int.cast_zero]
  dsimp [f, g]
  rw [hrpred] at hbound
  rw [hfactor]
  simp only [mul_assoc, ← mul_sum]
  linarith

theorem rowHolds_tail {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic)
    (r h : ℕ) (hr : 2 ≤ r) (hrv : r ≤ (S \ I).card) :
    RowHolds G S I (.tail r h) := by
  classical
  let f : ℕ → ℝ := fun m => deletionThresholdCoeff I.card r h m
  let g : ℕ → ℝ := fun m =>
    (((S \ I).card - (r - 1) : ℕ) : ℝ) * (if h ≤ m then 1 else 0)
  have hvalue := hI.rowValue_eq_two_layers (.tail r h) r (r - 1)
    (by omega) hrv (by omega) (by omega) f g (by
      intro p _
      simp only [coeff, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
        Int.cast_ite, Int.cast_one, Int.cast_zero]
      rw [← card_sdiff_of_subset hI.subset]
      dsimp [f, g]
      ring)
  have hbound := hI.tail_layer_inequality hG r hr hrv h
  have hfactor : (((S \ I).card - (r - 1) : ℕ) : ℝ) =
      ((S \ I).card : ℝ) - (r : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    ring
  unfold RowHolds
  rw [hvalue]
  simp only [rhs, Int.cast_zero]
  dsimp [f, g]
  rw [hfactor]
  simp only [mul_assoc, ← mul_sum]
  linarith

theorem rowHolds_union {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (r : ℕ)
    (hr : 1 ≤ r) (hrv : r ≤ (S \ I).card) :
    RowHolds G S I (.unionRow r) := by
  classical
  let f : ℕ → ℝ := fun m => (I.card : ℝ) - m
  let g : ℕ → ℝ := fun m =>
    (((S \ I).card - 1).choose (r - 1) : ℝ) * ((I.card : ℝ) - m)
  have hvalue := hI.rowValue_eq_two_layers (.unionRow r) r 1
    hr hrv (by omega) (by omega) f g (by
      intro p _
      simp only [coeff, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      rw [← card_sdiff_of_subset hI.subset]
      dsimp [f, g]
      ring)
  have hbound := coverage_union_layer G I (S \ I) r hr
  unfold RowHolds
  rw [hvalue]
  simp only [rhs, Int.cast_zero]
  dsimp [f, g]
  simp only [mul_assoc, ← mul_sum]
  linarith

/-- Hall rows include r=0; the omitted zero layer is exactly the RHS constant.
The structural extension theorem needs only r<v, with no restriction on l. -/
theorem rowHolds_hall {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic)
    (r l : ℕ) (hrv : r < (S \ I).card) : RowHolds G S I (.hall r l) := by
  classical
  let H : ℕ → ℝ := fun j => ∑ m ∈ range (I.card + 1),
    (m.choose l : ℝ) * (layerCount G I (S \ I) j m : ℝ)
  let f : ℕ → ℝ := fun m => ((r + 1 : ℕ) : ℝ) * (m.choose l : ℝ)
  let g : ℕ → ℝ := fun m =>
    (hallFactor S.card I.card r l : ℝ) * (m.choose l : ℝ)
  have hfactor : hallFactor S.card I.card r l =
      (S \ I).card - r - (l - (I.card - (S \ I).card)) := by
    simp only [hallFactor, card_sdiff_of_subset hI.subset]
  have hbound : ((r + 1 : ℕ) : ℝ) * H (r + 1) ≤
      (hallFactor S.card I.card r l : ℝ) * H r := by
    rw [hfactor]
    have hn := hI.hallCount_extension_bound hG r l
    unfold hallCount at hn
    dsimp [H]
    exact_mod_cast hn
  have hcoeff (p : ℕ × ℕ) : (coeff S.card I.card (.hall r l) p : ℝ) =
      (indicator p.1 (r + 1) : ℝ) * f p.2 - (indicator p.1 r : ℝ) * g p.2 := by
    simp only [coeff, Int.cast_mul, Int.cast_sub, Int.cast_natCast]
    dsimp [f, g]
    ring
  by_cases hrzero : r = 0
  · subst r
    have hvalue : rowValue G S I (.hall 0 l) = H 1 := by
      unfold rowValue
      simp_rw [hcoeff, sub_mul]
      rw [sum_sub_distrib, hI.sum_indicator_layer 1 (by omega) (by omega),
        sum_indicator_zero, sub_zero]
      simp only [f, Nat.zero_add, Nat.cast_one, one_mul]
      rfl
    have hzero : H 0 = (I.card.choose l : ℝ) :=
      sum_layer_zero G I (S \ I) (fun m => (m.choose l : ℝ))
    rw [hzero] at hbound
    unfold RowHolds
    rw [hvalue]
    simpa only [rhs, ↓reduceIte, Int.cast_mul, Int.cast_natCast,
      Nat.zero_add, Nat.cast_one, one_mul] using hbound
  · have hvalue := hI.rowValue_eq_two_layers (.hall r l) (r + 1) r
      (by omega) (by omega) (by omega) (by omega) f g (fun p _ => hcoeff p)
    have hvalue' : rowValue G S I (.hall r l) =
        ((r + 1 : ℕ) : ℝ) * H (r + 1) - (hallFactor S.card I.card r l : ℝ) * H r := by
      rw [hvalue]
      simp only [f, g, H, mul_assoc, ← mul_sum]
    unfold RowHolds
    rw [hvalue']
    simp only [rhs, hrzero, ↓reduceIte, Int.cast_zero]
    linarith

#print axioms rowHolds_count
#print axioms rowHolds_path
#print axioms rowHolds_private
#print axioms rowHolds_tail
#print axioms rowHolds_union
#print axioms rowHolds_hall
end FiniteRows
end ForestUnimodality
