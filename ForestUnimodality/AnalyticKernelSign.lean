import ForestUnimodality.HardCoreMoments
import ForestUnimodality.FiniteAssembly

/-! A positive nonnegative mixture of the three tilted kernels excludes a
weak valley in the original coefficient sequence. This is only the algebraic
interpretation of a kernel; positivity of any analytic certificate remains a
separate obligation. -/

namespace ForestUnimodality

noncomputable def tiltedProbability (c : ℕ → ℕ) (z Z : ℝ) (k : ℕ) : ℝ :=
  (c k : ℝ) * z ^ k / Z

noncomputable def tiltedLeft (c : ℕ → ℕ) (z Z : ℝ) (k : ℕ) : ℝ :=
  (1 - z / (1 + z)) * tiltedProbability c z Z k -
    (z / (1 + z)) * tiltedProbability c z Z (k - 1)

noncomputable def tiltedRight (c : ℕ → ℕ) (z Z : ℝ) (k : ℕ) : ℝ :=
  (z / (1 + z)) * tiltedProbability c z Z k -
    (1 - z / (1 + z)) * tiltedProbability c z Z (k + 1)

noncomputable def tiltedCenter (c : ℕ → ℕ) (z Z : ℝ) (k : ℕ) : ℝ :=
  2 * tiltedProbability c z Z k - tiltedProbability c z Z (k - 1) -
    tiltedProbability c z Z (k + 1)

theorem tiltedLeft_eq (c : ℕ → ℕ) {z Z : ℝ} (hz : 0 < z) (hZ : 0 < Z)
    {k : ℕ} (hk : 1 ≤ k) :
    tiltedLeft c z Z k = z ^ k / (Z * (1 + z)) *
      ((c k : ℝ) - (c (k - 1) : ℝ)) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hZne := ne_of_gt hZ
  have hsum : 1 + z ≠ 0 := by positivity
  simp only [tiltedLeft, tiltedProbability, Nat.succ_eq_add_one, Nat.add_sub_cancel,
    pow_succ]
  field_simp
  ring

theorem tiltedRight_eq (c : ℕ → ℕ) {z Z : ℝ} (hz : 0 < z) (hZ : 0 < Z)
    (k : ℕ) :
    tiltedRight c z Z k = z ^ (k + 1) / (Z * (1 + z)) *
      ((c k : ℝ) - (c (k + 1) : ℝ)) := by
  have hZne := ne_of_gt hZ
  have hsum : 1 + z ≠ 0 := by positivity
  simp only [tiltedRight, tiltedProbability, pow_succ]
  field_simp
  ring

theorem tiltedCenter_eq (c : ℕ → ℕ) (z Z : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    tiltedCenter c z Z k = -(z ^ (k - 1) / Z) *
      ((z - 1) ^ 2 * (c k : ℝ) + ((c (k - 1) : ℝ) - (c k : ℝ)) +
        z ^ 2 * ((c (k + 1) : ℝ) - (c k : ℝ))) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [tiltedCenter, tiltedProbability, Nat.succ_eq_add_one,
    Nat.add_sub_cancel, pow_succ, div_eq_mul_inv]
  ring

theorem tilted_kernels_nonpositive_of_weak_valley (c : ℕ → ℕ)
    {z Z : ℝ} (hz : 0 < z) (hZ : 0 < Z) {k : ℕ} (hk : 1 ≤ k)
    (hleft : c k ≤ c (k - 1)) (hright : c k ≤ c (k + 1)) :
    tiltedLeft c z Z k ≤ 0 ∧ tiltedRight c z Z k ≤ 0 ∧ tiltedCenter c z Z k ≤ 0 := by
  have hl : (c k : ℝ) ≤ (c (k - 1) : ℝ) := by exact_mod_cast hleft
  have hr : (c k : ℝ) ≤ (c (k + 1) : ℝ) := by exact_mod_cast hright
  refine ⟨?_, ?_, ?_⟩
  · rw [tiltedLeft_eq c hz hZ hk]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hl)
  · rw [tiltedRight_eq c hz hZ k]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hr)
  · rw [tiltedCenter_eq c z Z hk]
    have hinside : 0 ≤ (z - 1) ^ 2 * (c k : ℝ) +
        ((c (k - 1) : ℝ) - (c k : ℝ)) + z ^ 2 * ((c (k + 1) : ℝ) - (c k : ℝ)) := by
      exact add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
        (sub_nonneg.mpr hl)) (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hr))
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg (pow_nonneg hz.le _) hZ.le)) hinside

/-- Strict positivity excludes the entire weak-valley condition, including
equalities. No claim of strict log-concavity is made. -/
theorem no_weak_valley_of_positive_tilted_kernel (c : ℕ → ℕ)
    {z Z wL wR wC : ℝ} (hz : 0 < z) (hZ : 0 < Z)
    (hwL : 0 ≤ wL) (hwR : 0 ≤ wR) (hwC : 0 ≤ wC)
    {k : ℕ} (hk : 1 ≤ k)
    (hpositive : 0 < wL * tiltedLeft c z Z k + wR * tiltedRight c z Z k +
      wC * tiltedCenter c z Z k) :
    ¬ (c k ≤ c (k - 1) ∧ c k ≤ c (k + 1)) := by
  rintro ⟨hl, hr⟩
  obtain ⟨hl', hr', hc'⟩ := tilted_kernels_nonpositive_of_weak_valley c hz hZ hk hl hr
  have hL := mul_nonpos_of_nonneg_of_nonpos hwL hl'
  have hR := mul_nonpos_of_nonneg_of_nonpos hwR hr'
  have hC := mul_nonpos_of_nonneg_of_nonpos hwC hc'
  linarith

theorem alternative_of_positive_tilted_kernel (c : ℕ → ℕ)
    {z Z wL wR wC : ℝ} (hz : 0 < z) (hZ : 0 < Z)
    (hwL : 0 ≤ wL) (hwR : 0 ≤ wR) (hwC : 0 ≤ wC)
    {k : ℕ} (hk : 1 ≤ k)
    (hpositive : 0 < wL * tiltedLeft c z Z k + wR * tiltedRight c z Z k +
      wC * tiltedCenter c z Z k) :
    CertificateAlternative c k := by
  have h := no_weak_valley_of_positive_tilted_kernel c hz hZ hwL hwR hwC hk hpositive
  by_cases hl : c (k - 1) < c k
  · exact Or.inl hl
  · exact Or.inr (Or.inl (by omega))

#print axioms tiltedLeft_eq
#print axioms tiltedRight_eq
#print axioms tiltedCenter_eq
#print axioms no_weak_valley_of_positive_tilted_kernel
#print axioms alternative_of_positive_tilted_kernel

end ForestUnimodality
