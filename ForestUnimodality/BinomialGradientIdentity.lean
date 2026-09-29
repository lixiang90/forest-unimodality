import ForestUnimodality.BinomialFourier

/-! Exact adjacent-binomial differences at all integer indices. -/
namespace ForestUnimodality

theorem binomialMass_eq_zero_of_neg (n : ℕ) {j : ℤ} (hj : j < 0) (q : ℝ) :
    binomialMass n j q = 0 := by simp [binomialMass, not_le.mpr hj]

theorem binomialMass_eq_zero_of_gt (n : ℕ) {j : ℤ} (hj : (n : ℤ) < j) (q : ℝ) :
    binomialMass n j q = 0 := by simp [binomialMass, not_le.mpr hj]

private theorem gradient_identity_interior (n k : ℕ) (hk : k + 1 ≤ n) (q : ℝ) :
    ((n + 1 : ℕ) : ℝ) * (q * (1 - q)) *
      (binomialMass n ((k + 1 : ℕ) : ℤ) q - binomialMass n k q) =
      (((n + 1 : ℕ) : ℝ) * q - (k + 1 : ℕ)) * binomialMass (n + 1) ((k + 1 : ℕ) : ℤ) q := by
  have hc : ((n + 1).choose (k + 1) : ℝ) = (n.choose k : ℝ) + (n.choose (k + 1) : ℝ) := by
    exact_mod_cast Nat.choose_succ_succ' n k
  have hm : ((n + 1 : ℕ) : ℝ) * (n.choose k : ℝ) =
      ((n + 1).choose (k + 1) : ℝ) * (k + 1 : ℕ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  rw [binomialMass_nat, binomialMass_nat, binomialMass_nat]
  have he1 : n - k = (n - (k + 1)) + 1 := by omega
  have he2 : n + 1 - (k + 1) = (n - (k + 1)) + 1 := by omega
  rw [he1, he2, pow_succ, pow_succ]
  linear_combination
    q ^ (k + 1) * (1 - q) ^ (n - (k + 1)) * (1 - q) *
      (-((n + 1 : ℕ) : ℝ) * q * hc - hm)

/-- The division-free identity remains valid at q=0 and q=1. It includes both
support endpoints and all integer indices outside the support. -/
theorem binomial_gradient_identity_mul (n : ℕ) (j : ℤ) (q : ℝ) :
    ((n + 1 : ℕ) : ℝ) * (q * (1 - q)) *
      (binomialMass n j q - binomialMass n (j - 1) q) =
      (((n + 1 : ℕ) : ℝ) * q - (j : ℝ)) * binomialMass (n + 1) j q := by
  by_cases hj0 : 0 ≤ j
  · lift j to ℕ using hj0
    cases j with
    | zero =>
      rw [binomialMass_nat, binomialMass_eq_zero_of_neg n (by norm_num), binomialMass_nat]
      simp only [Nat.choose_zero_right, pow_zero, Nat.sub_zero, sub_zero,
        Int.cast_zero, Nat.cast_zero]
      rw [pow_succ]
      ring
    | succ k =>
      have hjprev : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
      rw [hjprev]
      by_cases hk : k + 1 ≤ n
      · convert gradient_identity_interior n k hk q using 1
        push_cast
        ring
      · by_cases hkn : k = n
        · subst k
          rw [binomialMass_eq_zero_of_gt n (by omega), binomialMass_nat, binomialMass_nat]
          simp only [Nat.choose_self, Nat.sub_self, pow_zero, mul_one, zero_sub]
          push_cast
          rw [pow_succ]
          ring
        · have hnk : n < k := by omega
          rw [binomialMass_eq_zero_of_gt n (by omega),
            binomialMass_eq_zero_of_gt n (by exact_mod_cast hnk),
            binomialMass_eq_zero_of_gt (n + 1) (by omega)]
          ring
  · rw [binomialMass_eq_zero_of_neg n (by omega),
      binomialMass_eq_zero_of_neg n (by omega), binomialMass_eq_zero_of_neg (n + 1) (by omega)]
    ring

/-- The exact finite identity used to locate the extremal gradient. -/
theorem binomial_gradient_identity (n : ℕ) (j : ℤ) {q : ℝ}
    (hv : q * (1 - q) ≠ 0) :
    binomialMass n j q - binomialMass n (j - 1) q =
      ((((n + 1 : ℕ) : ℝ) * q - (j : ℝ)) /
        (((n + 1 : ℕ) : ℝ) * (q * (1 - q)))) * binomialMass (n + 1) j q := by
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (mul_ne_zero hn hv)).mpr
  rw [mul_comm, binomial_gradient_identity_mul]

#print axioms binomial_gradient_identity_mul
#print axioms binomial_gradient_identity
end ForestUnimodality
