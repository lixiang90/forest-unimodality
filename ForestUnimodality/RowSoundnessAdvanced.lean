import ForestUnimodality.RowSemantics
import ForestUnimodality.MeanInequality
import ForestUnimodality.EdgeUpperInequality
import ForestUnimodality.RowSummation

/-! Soundness of advanced executable integer rows on actual graph layers. -/

namespace ForestUnimodality
namespace FiniteRows

open Finset

variable {V : Type*} [DecidableEq V]

theorem complement_card_eq (G : SimpleGraph V) {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) : S.card - I.card = (S \ I).card :=
  (card_sdiff_of_subset hI.subset).symm

theorem cast_meanBeta {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (r : ℕ) :
    (meanBeta S.card I.card r : ℝ) =
      (((S \ I).card - 2).choose (r - 1) : ℝ) -
        ((I.card : ℝ) - 2) * (((S \ I).card - 2).choose (r - 2) : ℝ) := by
  simp [meanBeta, complement_card_eq G hI]

theorem cast_meanBase {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (r : ℕ) :
    (meanBase S.card I.card r : ℝ) =
      (I.card : ℝ) * (((S \ I).card - 2).choose r : ℝ) +
        ((I.card : ℝ) - ((S \ I).card : ℝ) + 1) *
          (((S \ I).card - 2).choose (r - 1) : ℝ) := by
  have hsum : I.card + (S \ I).card = S.card := by
    have hsub := card_sdiff_add_card_eq_card hI.subset
    omega
  have hsumR : (S.card : ℝ) = (I.card : ℝ) + ((S \ I).card : ℝ) := by
    exact_mod_cast hsum.symm
  simp only [meanBase, complement_card_eq G hI, Int.cast_add, Int.cast_mul,
    Int.cast_sub, Int.cast_natCast, Int.cast_ofNat, Int.cast_one]
  rw [hsumR]
  ring

theorem real_edge_count_identity (G : SimpleGraph V) (Y : Finset V) :
    (edgeCountOn G Y : ℝ) + (countIndependent G Y 2 : ℝ) = (Y.card.choose 2 : ℝ) := by
  have h := countIndependent_add_card_badSubsetsOn G Y 2
  change countIndependent G Y 2 + edgeCountOn G Y = Y.card.choose 2 at h
  exact_mod_cast (by omega : edgeCountOn G Y + countIndependent G Y 2 = Y.card.choose 2)

theorem real_layer_mass (G : SimpleGraph V) (I Y : Finset V) (r : ℕ) :
    (∑ m ∈ range (I.card + 1), (layerCount G I Y r m : ℝ)) =
      (countIndependent G Y r : ℝ) := by
  exact_mod_cast sum_layerCount_eq_countIndependent G I Y r

/-- Additive evaluation keeps both contributions even when the two source
layers coincide, as happens for the mean row at r=2. -/
theorem rowValue_of_two_layers {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (row : Row) (r s : ℕ)
    (hr : 1 ≤ r) (hrv : r ≤ (S \ I).card) (hs : 1 ≤ s) (hsv : s ≤ (S \ I).card)
    (f g : ℕ → ℝ)
    (hcoeff : ∀ p, (coeff S.card I.card row p : ℝ) =
      (indicator p.1 r : ℝ) * f p.2 + (indicator p.1 s : ℝ) * g p.2) :
    rowValue G S I row =
      (∑ m ∈ range (I.card + 1), f m * (layerCount G I (S \ I) r m : ℝ)) +
        ∑ m ∈ range (I.card + 1), g m * (layerCount G I (S \ I) s m : ℝ) := by
  unfold rowValue
  simp_rw [hcoeff, add_mul]
  rw [sum_add_distrib, hI.sum_indicator_layer r hr hrv f,
    hI.sum_indicator_layer s hs hsv g]

theorem rowHolds_mean {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic)
    (r : ℕ) (hr : 2 ≤ r) (hrv : r ≤ (S \ I).card) : RowHolds G S I (.mean r) := by
  have hv := complement_card_eq G hI
  have hv2 : 2 ≤ (S \ I).card := by omega
  have hrow := rowValue_of_two_layers hI (.mean r) r 2 (by omega) hrv (by omega) hv2
    (fun m => -(m : ℝ)) (fun _ => -(meanBeta S.card I.card r : ℝ)) (by
      intro p
      simp only [coeff, Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_natCast]
      ring)
  have hrow' : rowValue G S I (.mean r) =
      -(∑ m ∈ range (I.card + 1), (m : ℝ) * (layerCount G I (S \ I) r m : ℝ)) -
        (meanBeta S.card I.card r : ℝ) * (countIndependent G (S \ I) 2 : ℝ) := by
    rw [hrow]
    simp only [neg_mul, sum_neg_distrib, ← mul_sum, real_layer_mass]
    ring
  have hmean := hI.mean_layer_inequality hG r hr hv2
  rw [← cast_meanBase hI r, ← cast_meanBeta hI r] at hmean
  have he := real_edge_count_identity G (S \ I)
  unfold RowHolds
  rw [hrow']
  simp only [rhs, Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_natCast, hv]
  rw [← he]
  nlinarith

theorem rowHolds_edgeLower {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I)
    (r : ℕ) (hr : 2 ≤ r) (hrv : r ≤ (S \ I).card) : RowHolds G S I (.edgeLower r) := by
  have hv := complement_card_eq G hI
  have hv2 : 2 ≤ (S \ I).card := by omega
  have hrow := rowValue_of_two_layers hI (.edgeLower r) r 2 (by omega) hrv (by omega) hv2
    (fun _ => -1) (fun _ => (((S \ I).card - 2).choose (r - 2) : ℝ)) (by
      intro p
      simp only [coeff, Int.cast_add, Int.cast_neg, Int.cast_mul, Int.cast_natCast, hv]
      ring)
  have hrow' : rowValue G S I (.edgeLower r) =
      -(countIndependent G (S \ I) r : ℝ) +
        (((S \ I).card - 2).choose (r - 2) : ℝ) * (countIndependent G (S \ I) 2 : ℝ) := by
    rw [hrow]
    simp only [neg_one_mul, sum_neg_distrib, ← mul_sum, real_layer_mass]
  have hnat := choose_le_countIndependent_add_edgeCountOn_mul_choose G (S \ I) r hr
  have hb : (((S \ I).card).choose r : ℝ) ≤ (countIndependent G (S \ I) r : ℝ) +
      (edgeCountOn G (S \ I) : ℝ) * (((S \ I).card - 2).choose (r - 2) : ℝ) := by
    exact_mod_cast hnat
  have he := real_edge_count_identity G (S \ I)
  unfold RowHolds
  rw [hrow']
  simp only [rhs, Int.cast_add, Int.cast_neg, Int.cast_mul, Int.cast_natCast, hv]
  nlinarith

theorem rowHolds_releaseUpper {G : SimpleGraph V} {S I : Finset V}
    (hmin : IsEdgeMinimalMaximumOn G S I) (hG : G.IsAcyclic)
    (r h : ℕ) (hr : 2 ≤ r) (hrv : r ≤ (S \ I).card) :
    RowHolds G S I (.releaseUpper r h) := by
  have hI := hmin.1
  have hv := complement_card_eq G hI
  have hrow := rowValue_of_two_layers hI (.releaseUpper r h) (r - 1) r
    (by omega) (by omega) (by omega) hrv
    (fun m => (extensionFactor S.card I.card r : ℝ) * max 0 ((m : ℝ) - (h : ℝ)))
    (fun m => -(releaseUpperCoeff I.card r h m : ℝ)) (by
      intro p
      simp only [coeff, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_max,
        Int.cast_zero]
      ring)
  have hrow' : rowValue G S I (.releaseUpper r h) =
      (extensionFactor S.card I.card r : ℝ) *
        (∑ m ∈ range (I.card + 1), max 0 ((m : ℝ) - (h : ℝ)) *
          (layerCount G I (S \ I) (r - 1) m : ℝ)) -
      ∑ m ∈ range (I.card + 1), (releaseUpperCoeff I.card r h m : ℝ) *
        (layerCount G I (S \ I) r m : ℝ) := by
    rw [hrow]
    simp only [mul_assoc, ← mul_sum, neg_mul, sum_neg_distrib, sub_eq_add_neg]
  have hb := hI.release_upper_layer_of_edge_budget r hr h
    (I.card - (S \ I).card - 1) (hmin.edgeCountOn_complement_le hG)
  have hf : extensionFactor S.card I.card r =
      (S \ I).card - (r - 1) - (I.card - (S \ I).card - 1) := by
    simp only [extensionFactor, sparseBudget, hv]
  unfold RowHolds
  rw [hrow', hf]
  simpa only [rhs, Int.cast_zero] using sub_nonpos.mpr hb

theorem rowHolds_tailUpper {G : SimpleGraph V} {S I : Finset V}
    (hmin : IsEdgeMinimalMaximumOn G S I) (hG : G.IsAcyclic)
    (r h : ℕ) (hr : 2 ≤ r) (hrv : r ≤ (S \ I).card) :
    RowHolds G S I (.tailUpper r h) := by
  have hI := hmin.1
  have hv := complement_card_eq G hI
  have hrow := rowValue_of_two_layers hI (.tailUpper r h) (r - 1) r
    (by omega) (by omega) (by omega) hrv
    (fun m => (extensionFactor S.card I.card r : ℝ) * (if h ≤ m then 1 else 0))
    (fun m => -(thresholdUpperCoeff I.card r h m : ℝ)) (by
      intro p
      simp only [coeff, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      split_ifs <;> simp
      all_goals ring)
  have hrow' : rowValue G S I (.tailUpper r h) =
      (extensionFactor S.card I.card r : ℝ) *
        (∑ m ∈ range (I.card + 1), (if h ≤ m then (1 : ℝ) else 0) *
          (layerCount G I (S \ I) (r - 1) m : ℝ)) -
      ∑ m ∈ range (I.card + 1), (thresholdUpperCoeff I.card r h m : ℝ) *
        (layerCount G I (S \ I) r m : ℝ) := by
    rw [hrow]
    simp only [mul_assoc, ← mul_sum, neg_mul, sum_neg_distrib, sub_eq_add_neg]
  have hb := hI.tail_upper_layer_of_edge_budget r hr h
    (I.card - (S \ I).card - 1) (hmin.edgeCountOn_complement_le hG)
  have hf : extensionFactor S.card I.card r =
      (S \ I).card - (r - 1) - (I.card - (S \ I).card - 1) := by
    simp only [extensionFactor, sparseBudget, hv]
  unfold RowHolds
  rw [hrow', hf]
  simpa only [rhs, Int.cast_zero] using sub_nonpos.mpr hb

theorem rowHolds_edgeUpper {G : SimpleGraph V} {S I : Finset V}
    (hmin : IsEdgeMinimalMaximumOn G S I) (hG : G.IsAcyclic)
    (r : ℕ) (hr : 2 ≤ r) (hrv : r ≤ (S \ I).card) :
    RowHolds G S I (.edgeUpper r) := by
  have hI := hmin.1
  have hv := complement_card_eq G hI
  by_cases hD : intrinsicBudget S.card I.card = 0
  · have hrow : rowValue G S I (.edgeUpper r) =
        (countIndependent G (S \ I) r : ℝ) := by
      simp only [rowValue, coeff, hD, if_true]
      exact hI.sum_indicator_count r (by omega) hrv
    unfold RowHolds
    rw [hrow]
    simpa only [rhs, hD, if_true, Int.cast_natCast, hv] using
      countIndependent_edge_upper_zero_budget G (S \ I) r
  · have hv2 : 2 ≤ (S \ I).card := by omega
    have hrow := rowValue_of_two_layers hI (.edgeUpper r) r 2
      (by omega) hrv (by omega) hv2
      (fun _ => (intrinsicBudget S.card I.card : ℝ))
      (fun _ => -(edgeGap (S.card - I.card) (intrinsicBudget S.card I.card) r : ℝ)) (by
        intro p
        simp only [coeff, hD, if_false, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
        ring)
    have hrow' : rowValue G S I (.edgeUpper r) =
        (intrinsicBudget S.card I.card : ℝ) * (countIndependent G (S \ I) r : ℝ) -
          (edgeGap (S.card - I.card) (intrinsicBudget S.card I.card) r : ℝ) *
            (countIndependent G (S \ I) 2 : ℝ) := by
      rw [hrow]
      simp only [neg_mul, sum_neg_distrib, ← mul_sum, real_layer_mass, sub_eq_add_neg]
    have hbudget : intrinsicBudget S.card I.card =
        min (I.card - (S \ I).card - 1) ((S \ I).card - 1) := by
      simp only [intrinsicBudget, sparseBudget, hv]
    have hpos : 1 ≤ min (I.card - (S \ I).card - 1) ((S \ I).card - 1) := by
      rw [← hbudget]
      omega
    have hb := hmin.edge_upper_row hG hpos r hr
    unfold RowHolds
    rw [hrow']
    simp only [rhs]
    rw [if_neg hD]
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      hv, hbudget, edgeGap, edgeUpperGap] using hb

#print axioms rowHolds_mean
#print axioms rowHolds_releaseUpper
#print axioms rowHolds_tailUpper
#print axioms rowHolds_edgeLower
#print axioms rowHolds_edgeUpper

end FiniteRows
end ForestUnimodality
