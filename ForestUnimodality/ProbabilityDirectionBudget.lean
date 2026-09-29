import ForestUnimodality.BinomialKernel

/-! A point-mass lower bound and an absolute gradient upper bound imply
positivity of the activity-weighted directional kernel. -/
namespace ForestUnimodality.ProbabilityDirectionBudget

theorem left_numeric {u v z b A B : ℝ} (hz : 0 ≤ z) (hzb : z ≤ b)
    (hb : b ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : A ≤ u)
    (hgrad : v - u ≤ B) : (1 - b) * A - b * B ≤ u - z * v := by
  have h1 := mul_le_mul_of_nonneg_left hu (show 0 ≤ 1 - z by linarith)
  have h2 := mul_le_mul_of_nonneg_left hgrad hz
  have h3 := mul_nonneg (sub_nonneg.mpr hzb) (add_nonneg hA hB)
  nlinarith

theorem right_numeric {u v z a A B : ℝ} (haz : a ≤ z) (ha : 1 ≤ a)
    (hA : 0 ≤ A) (hu : A ≤ u) (hgrad : v - u ≤ B) :
    (a - 1) * A - B ≤ z * u - v := by
  have h1 := mul_le_mul_of_nonneg_left hu (show 0 ≤ z - 1 by linarith)
  have h2 := mul_nonneg (sub_nonneg.mpr haz) hA
  nlinarith

theorem left_positive (c : ℕ → ℕ) {z Z scale b A B : ℝ} (k : ℕ)
    (hz : 0 < z) (hs : 0 < scale) (hzb : z ≤ b) (hb : b ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hmass : A ≤ scale * tiltedProbability c z Z k)
    (hgrad : scale * |tiltedProbability c z Z (k - 1) - tiltedProbability c z Z k| ≤ B)
    (hbudget : 0 < (1 - b) * A - b * B) : 0 < tiltedLeft c z Z k := by
  have hg : scale * tiltedProbability c z Z (k - 1) -
      scale * tiltedProbability c z Z k ≤ B := by
    have h := mul_le_mul_of_nonneg_left
      (le_abs_self (tiltedProbability c z Z (k - 1) - tiltedProbability c z Z k)) hs.le
    rw [mul_sub] at h
    exact h.trans hgrad
  have hn := left_numeric hz.le hzb hb hA hB hmass hg
  have he : scale * tiltedProbability c z Z k -
      z * (scale * tiltedProbability c z Z (k - 1)) =
        (scale * (1 + z)) * tiltedLeft c z Z k := by
    unfold tiltedLeft
    field_simp
    ring
  rw [he] at hn
  exact (mul_pos_iff_of_pos_left (mul_pos hs (by linarith))).mp (hbudget.trans_le hn)

theorem right_positive (c : ℕ → ℕ) {z Z scale a A B : ℝ} (k : ℕ)
    (hz : 0 < z) (hs : 0 < scale) (haz : a ≤ z) (ha : 1 ≤ a)
    (hA : 0 ≤ A) (hmass : A ≤ scale * tiltedProbability c z Z k)
    (hgrad : scale * |tiltedProbability c z Z (k + 1) - tiltedProbability c z Z k| ≤ B)
    (hbudget : 0 < (a - 1) * A - B) : 0 < tiltedRight c z Z k := by
  have hg : scale * tiltedProbability c z Z (k + 1) -
      scale * tiltedProbability c z Z k ≤ B := by
    have h := mul_le_mul_of_nonneg_left
      (le_abs_self (tiltedProbability c z Z (k + 1) - tiltedProbability c z Z k)) hs.le
    rw [mul_sub] at h
    exact h.trans hgrad
  have hn := right_numeric haz ha hA hmass hg
  have he : z * (scale * tiltedProbability c z Z k) -
      scale * tiltedProbability c z Z (k + 1) =
        (scale * (1 + z)) * tiltedRight c z Z k := by
    unfold tiltedRight
    field_simp
    ring
  rw [he] at hn
  exact (mul_pos_iff_of_pos_left (mul_pos hs (by linarith))).mp (hbudget.trans_le hn)

theorem left_coefficient_lt (c : ℕ → ℕ) {z Z : ℝ} (hz : 0 < z)
    (hZ : 0 < Z) {k : ℕ} (hk : 1 ≤ k) (h : 0 < tiltedLeft c z Z k) :
    c (k - 1) < c k := by
  rw [tiltedLeft_eq c hz hZ hk] at h
  have hp : 0 < z ^ k / (Z * (1 + z)) := by positivity
  have hc := (mul_pos_iff_of_pos_left hp).mp h
  exact_mod_cast (sub_pos.mp hc)

theorem right_coefficient_lt (c : ℕ → ℕ) {z Z : ℝ} (hz : 0 < z)
    (hZ : 0 < Z) (k : ℕ) (h : 0 < tiltedRight c z Z k) :
    c (k + 1) < c k := by
  rw [tiltedRight_eq c hz hZ k] at h
  have hp : 0 < z ^ (k + 1) / (Z * (1 + z)) := by positivity
  have hc := (mul_pos_iff_of_pos_left hp).mp h
  exact_mod_cast (sub_pos.mp hc)

#print axioms left_positive
#print axioms right_positive
#print axioms left_coefficient_lt
#print axioms right_coefficient_lt
end ForestUnimodality.ProbabilityDirectionBudget
