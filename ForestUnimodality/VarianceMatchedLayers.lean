import ForestUnimodality.LaplaceRateInterval
import ForestUnimodality.LowerTailCharges

/-! Shifting the available count by the triangular variance preserves the
actual joint layer law. The tail exponent retains the original mean m. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

noncomputable def shiftedAvailableRatio (G : SimpleGraph V) (S B : Finset V)
    (z c : ℝ) (M : ℕ) : ℝ := ((M : ℝ)+c)/(hardCoreAvailableMean G S B z+c)

theorem hardCoreLayerExpectation_const (G : SimpleGraph V) (S B : Finset V)
    (hBS : B ⊆ S) (hB : G.IsIndepSet (B : Set V)) {z : ℝ} (hz : 0 ≤ z) (a : ℝ) :
    hardCoreLayerExpectation G S B z (fun _ _ => a) = a := by
  simp only [hardCoreLayerExpectation, ← sum_mul, sum_hardCoreLayerWeight G S B hBS hB hz, one_mul]

theorem hardCoreLayerExpectation_shifted_ratio (G : SimpleGraph V) (S B : Finset V)
    (hBS : B ⊆ S) (hB : G.IsIndepSet (B : Set V)) {z c : ℝ}
    (hz : 0 ≤ z) (hc : 0 < c) :
    hardCoreLayerExpectation G S B z (fun _ M => shiftedAvailableRatio G S B z c M) = 1 := by
  have hden : hardCoreAvailableMean G S B z+c ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (hardCoreAvailableMean_nonneg G S B hz) hc)
  unfold hardCoreLayerExpectation shiftedAvailableRatio
  simp only [← mul_div_assoc, mul_add, ← sum_div, sum_add_distrib, ← sum_mul,
    sum_hardCoreLayerWeight G S B hBS hB hz, one_mul]
  change (hardCoreAvailableMean G S B z+c)/(hardCoreAvailableMean G S B z+c)=1
  exact div_self hden

theorem hardCoreLayerExpectation_shifted_ratio_variance (G : SimpleGraph V)
    (S B : Finset V) (z c : ℝ) (hden : hardCoreAvailableMean G S B z+c ≠ 0) :
    hardCoreLayerExpectation G S B z (fun _ M => (shiftedAvailableRatio G S B z c M-1)^2) =
      hardCoreAvailableVariance G S B z/(hardCoreAvailableMean G S B z+c)^2 := by
  have hp (M : ℕ) : (shiftedAvailableRatio G S B z c M-1)^2 =
      ((M : ℝ)-hardCoreAvailableMean G S B z)^2/(hardCoreAvailableMean G S B z+c)^2 := by
    unfold shiftedAvailableRatio
    field_simp
    ring
  simp only [hardCoreLayerExpectation, hp, ← mul_div_assoc, ← sum_div,
    hardCoreAvailableVariance]

/-- Cancellation is performed pointwise before expectation, so M and the
conditional mean may remain arbitrarily correlated. -/
theorem hardCoreLayerExpectation_shifted_cross (G : SimpleGraph V) (S B : Finset V)
    (hBS : B ⊆ S) (hB : G.IsIndepSet (B : Set V)) {z c v k : ℝ}
    (hz : 0 < z) (hc : 0 < c) (hv : 0 < v) (hmean : hardCoreMean G S z = k) :
    hardCoreLayerExpectation G S B z (fun j M =>
      shiftedAvailableRatio G S B z c M *
        ((k-binomialLayerMean j M z)^2/(2*v*((M : ℝ)+c)))) =
      (hardCoreVariance G S z -
        (z/(1+z))*(1-z/(1+z))*hardCoreAvailableMean G S B z) /
          (2*v*(hardCoreAvailableMean G S B z+c)) := by
  have hp (j M : ℕ) : shiftedAvailableRatio G S B z c M *
      ((k-binomialLayerMean j M z)^2/(2*v*((M : ℝ)+c))) =
        (k-binomialLayerMean j M z)^2/(2*v*(hardCoreAvailableMean G S B z+c)) := by
    have hM : (M : ℝ)+c ≠ 0 := ne_of_gt (by positivity)
    unfold shiftedAvailableRatio
    field_simp
  simp only [hardCoreLayerExpectation, hp, ← mul_div_assoc, ← sum_div]
  rw [← hardCoreLayerExpectation, hardCoreLayerExpectation_centered_sq G S B hBS hB hz hmean]

theorem shifted_ratio_lt_imp_available_lt (m c t : ℝ) (M : ℕ)
    (hden : 0 < m+c) (hc : 0 ≤ c) (ht : t ≤ 1)
    (h : ((M : ℝ)+c)/(m+c) < t) : (M : ℝ) < t*m := by
  have he := (div_lt_iff₀ hden).mp h
  have hct := mul_le_mul_of_nonneg_right ht hc
  nlinarith

theorem hardCoreLayerExpectation_shifted_variance_le (G : SimpleGraph V) (S B : Finset V)
    {z c D : ℝ} (hm : 0 < hardCoreAvailableMean G S B z) (hc : 0 ≤ c) (hD : 0 ≤ D)
    (hv : hardCoreAvailableVariance G S B z ≤ D*hardCoreAvailableMean G S B z) :
    hardCoreLayerExpectation G S B z (fun _ M => (shiftedAvailableRatio G S B z c M-1)^2) ≤
      D/hardCoreAvailableMean G S B z := by
  have hden := add_pos_of_pos_of_nonneg hm hc
  rw [hardCoreLayerExpectation_shifted_ratio_variance G S B z c (ne_of_gt hden)]
  apply (div_le_div_iff₀ (sq_pos_of_pos hden) hm).mpr
  have h1 := mul_le_mul_of_nonneg_right hv hm.le
  have h2 := mul_nonneg hD (sq_nonneg c)
  have h3 := mul_nonneg (mul_nonneg hD hm.le) hc
  nlinarith

theorem hardCoreLayerExpectation_shifted_cross_le (G : SimpleGraph V) (S B : Finset V)
    (hBS : B ⊆ S) (hB : G.IsIndepSet (B : Set V)) {z c R k : ℝ}
    (hz : 0 < z) (hc : 0 < c) (hR : 0 ≤ R) (hmean : hardCoreMean G S z = k)
    (hvar : hardCoreVariance G S z ≤
      (R+1)*(z/(1+z))*(1-z/(1+z))*hardCoreAvailableMean G S B z) :
    hardCoreLayerExpectation G S B z (fun j M => shiftedAvailableRatio G S B z c M *
      ((k-binomialLayerMean j M z)^2/(2*(z/(1+z))*(1-z/(1+z))*((M : ℝ)+c)))) ≤ R/2 := by
  have hq : 0 < z/(1+z) := by positivity
  have hq1 : z/(1+z) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hv : 0 < (z/(1+z))*(1-z/(1+z)) := mul_pos hq (sub_pos.mpr hq1)
  have hp : 0 < hardCoreAvailableMean G S B z+c :=
    add_pos_of_nonneg_of_pos (hardCoreAvailableMean_nonneg G S B hz.le) hc
  have he := hardCoreLayerExpectation_shifted_cross G S B hBS hB hz hc hv hmean
  simp only [mul_assoc] at he ⊢
  rw [he]
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := mul_nonneg (mul_nonneg hR hv.le) hc.le
  nlinarith

/-- The old tail cutoff uses m, not m+c. -/
theorem hardCoreLayerExpectation_shifted_tail_le (G : SimpleGraph V) (S B : Finset V)
    {z c t : ℝ} (hz : 0 ≤ z) (hc : 0 < c) (ht : t ≤ 1) :
    hardCoreLayerExpectation G S B z
      (fun _ M => if shiftedAvailableRatio G S B z c M < t then 1 else 0) ≤
        hardCoreAvailableLowerTail G S B z (t*hardCoreAvailableMean G S B z) := by
  unfold hardCoreLayerExpectation hardCoreAvailableLowerTail
  apply sum_le_sum
  intro j _
  apply sum_le_sum
  intro M _
  apply mul_le_mul_of_nonneg_left _ (hardCoreLayerWeight_nonneg G S B hz j M)
  dsimp only
  by_cases h : shiftedAvailableRatio G S B z c M < t
  · have hM := shifted_ratio_lt_imp_available_lt (hardCoreAvailableMean G S B z) c t M
      (add_pos_of_nonneg_of_pos (hardCoreAvailableMean_nonneg G S B hz) hc) hc.le ht h
    simp [h,hM]
  · simp only [if_neg h]
    split_ifs <;> norm_num

theorem shifted_ratio_ge_of_good_event (m c α : ℝ) (M : ℕ)
    (hden : 0 < m+c) (hc : 0 ≤ c) (hα : α ≤ 1) (hM : α*m ≤ (M : ℝ)) :
    α ≤ ((M : ℝ)+c)/(m+c) := by
  apply (le_div_iff₀ hden).mpr
  nlinarith [mul_le_mul_of_nonneg_right hα hc]

theorem shifted_ratio_le_of_bad_event {m c cmax α : ℝ} (M : ℕ)
    (hm : 0 ≤ m) (hc : 0 < c) (hcc : c ≤ cmax) (hα : α ≤ 1)
    (hM : (M : ℝ) ≤ α*m) :
    ((M : ℝ)+c)/(m+c) ≤ (α*m+cmax)/(m+cmax) := by
  apply (div_le_div_iff₀ (add_pos_of_nonneg_of_pos hm hc)
    (add_pos_of_nonneg_of_pos hm (hc.trans_le hcc))).mpr
  have h1 := mul_le_mul_of_nonneg_right hM (add_pos_of_nonneg_of_pos hm (hc.trans_le hcc)).le
  have h2 := mul_nonneg (mul_nonneg hm (sub_nonneg.mpr hcc)) (sub_nonneg.mpr hα)
  nlinarith

#print axioms hardCoreLayerExpectation_shifted_ratio
#print axioms hardCoreLayerExpectation_shifted_ratio_variance
#print axioms hardCoreLayerExpectation_shifted_cross
#print axioms hardCoreLayerExpectation_shifted_tail_le
#print axioms hardCoreLayerExpectation_shifted_variance_le
#print axioms hardCoreLayerExpectation_shifted_cross_le
end ForestUnimodality
