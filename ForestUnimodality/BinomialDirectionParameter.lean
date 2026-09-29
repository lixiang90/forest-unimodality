import ForestUnimodality.BinomialParameterDerivative

/-! Exact degree elevation of the directional kernels, and their continuous
parameter derivatives. All identities retain the out-of-support indices. -/
namespace ForestUnimodality.BinomialParameterDerivative

theorem mass_elevate_q (n : ℕ) (j : ℤ) (q : ℝ) :
    ((n + 1 : ℕ) : ℝ) * q * binomialMass n (j - 1) q =
      (j : ℝ) * binomialMass (n + 1) j q := by
  by_cases hj : 0 ≤ j
  · lift j to ℕ using hj
    cases j with
    | zero => simp [binomialMass_eq_zero_of_neg n (by norm_num : (-1 : ℤ) < 0)]
    | succ j =>
      have he : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
      rw [he]
      by_cases hjn : j ≤ n
      · have hc : ((n + 1 : ℕ) : ℝ) * (n.choose j : ℝ) =
            ((n + 1).choose (j + 1) : ℝ) * (j + 1 : ℕ) := by
          exact_mod_cast Nat.add_one_mul_choose_eq n j
        rw [binomialMass_nat, binomialMass_nat]
        simp only [Nat.add_sub_add_right, pow_succ]
        push_cast
        push_cast at hc
        linear_combination q ^ j * (1 - q) ^ (n - j) * q * hc
      · rw [binomialMass_eq_zero_of_gt n (by omega),
          binomialMass_eq_zero_of_gt (n + 1) (by omega)]
        ring
  · rw [binomialMass_eq_zero_of_neg n (by omega),
      binomialMass_eq_zero_of_neg (n + 1) (by omega)]
    ring

theorem mass_elevate_complement (n : ℕ) (j : ℤ) (q : ℝ) :
    ((n + 1 : ℕ) : ℝ) * (1 - q) * binomialMass n j q =
      (((n + 1 : ℕ) : ℝ) - (j : ℝ)) * binomialMass (n + 1) j q := by
  by_cases hj : 0 ≤ j
  · lift j to ℕ using hj
    by_cases hjn : j ≤ n
    · have hc : (n.choose j : ℝ) * (n + 1 : ℕ) =
          ((n + 1).choose j : ℝ) * (n + 1 - j : ℕ) := by
        exact_mod_cast Nat.choose_mul_succ_eq n j
      have he : n + 1 - j = (n - j) + 1 := by omega
      rw [binomialMass_nat, binomialMass_nat, he, pow_succ]
      rw [Nat.cast_sub (by omega : j ≤ n + 1)] at hc
      push_cast
      push_cast at hc
      linear_combination q ^ j * (1 - q) ^ (n - j) * (1 - q) * hc
    · by_cases he : j = n + 1
      · subst j
        rw [binomialMass_eq_zero_of_gt n (by omega)]
        norm_num
      · rw [binomialMass_eq_zero_of_gt n (by omega),
          binomialMass_eq_zero_of_gt (n + 1) (by omega)]
        ring
  · rw [binomialMass_eq_zero_of_neg n (by omega),
      binomialMass_eq_zero_of_neg (n + 1) (by omega)]
    ring

noncomputable def leftFactor (n : ℕ) (j : ℤ) : ℝ :=
  (((n + 1 : ℕ) : ℝ) - 2 * (j : ℝ)) / (n + 1 : ℕ)

noncomputable def rightFactor (n : ℕ) (j : ℤ) : ℝ :=
  (2 * (j : ℝ) + 1 - (n : ℝ)) / (n + 1 : ℕ)

theorem left_degree_elevation (n : ℕ) (j : ℤ) (q : ℝ) :
    binomialKernel n j q 1 0 0 = leftFactor n j * binomialMass (n + 1) j q := by
  have hq := mass_elevate_q n j q
  have hc := mass_elevate_complement n j q
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [binomialKernel, one_mul, zero_mul, add_zero, leftFactor]
  apply (mul_left_cancel₀ hn)
  field_simp
  nlinarith [hq, hc]

theorem right_degree_elevation (n : ℕ) (j : ℤ) (q : ℝ) :
    binomialKernel n j q 0 1 0 = rightFactor n j * binomialMass (n + 1) (j + 1) q := by
  have hq := mass_elevate_q n (j + 1) q
  have hc := mass_elevate_complement n (j + 1) q
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [show j + 1 - 1 = j by omega] at hq
  simp only [binomialKernel, one_mul, zero_mul, zero_add, add_zero, rightFactor]
  apply (mul_left_cancel₀ hn)
  field_simp
  push_cast at hq hc ⊢
  nlinarith [hq, hc]

theorem massSecond_eq_zero_of_outside (n : ℕ) (j : ℤ)
    (hj : ¬ (0 ≤ j ∧ j ≤ n)) (q : ℝ) : massSecond n j q = 0 := by
  have hz : binomialMass n j = fun _ => (0 : ℝ) := by
    funext x
    simp [binomialMass, hj]
  have hd : massDerivative n j = fun _ => (0 : ℝ) := by
    funext x
    rw [← deriv_mass, hz, deriv_const]
  rw [← deriv_massDerivative, hd, deriv_const]

theorem abs_leftFactor_le_one (n : ℕ) (j : ℤ)
    (hj0 : 0 ≤ j) (hjn : j ≤ (n + 1 : ℕ)) : |leftFactor n j| ≤ 1 := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hj0' : (0 : ℝ) ≤ j := by exact_mod_cast hj0
  have hjn' : (j : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hjn
  rw [leftFactor, abs_div, abs_of_pos hn, div_le_one hn]
  rw [abs_le]
  constructor <;> linarith

theorem rightFactor_eq_neg_left (n : ℕ) (j : ℤ) :
    rightFactor n j = -leftFactor n (j + 1) := by
  unfold rightFactor leftFactor
  push_cast
  ring

noncomputable def leftDerivative (n : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  leftFactor n j * massDerivative (n + 1) j q

noncomputable def leftSecond (n : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  leftFactor n j * massSecond (n + 1) j q

noncomputable def rightDerivative (n : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  -leftDerivative n (j + 1) q

noncomputable def rightSecond (n : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  -leftSecond n (j + 1) q

theorem hasDerivAt_left (n : ℕ) (j : ℤ) (q : ℝ) :
    HasDerivAt (fun x => binomialKernel n j x 1 0 0) (leftDerivative n j q) q := by
  have h := (hasDerivAt_mass (n + 1) j q).const_mul (leftFactor n j)
  convert h using 1 <;> first
    | rfl
    | (funext x; exact left_degree_elevation n j x)

theorem hasDerivAt_leftDerivative (n : ℕ) (j : ℤ) (q : ℝ) :
    HasDerivAt (leftDerivative n j) (leftSecond n j q) q := by
  exact (hasDerivAt_massDerivative (n + 1) j q).const_mul (leftFactor n j)

theorem hasDerivAt_right (n : ℕ) (j : ℤ) (q : ℝ) :
    HasDerivAt (fun x => binomialKernel n j x 0 1 0) (rightDerivative n j q) q := by
  have h := (hasDerivAt_left n (j + 1) q).neg
  convert h using 1 <;> first
    | rfl
    | (funext x; simp only [Pi.neg_apply, left_degree_elevation, right_degree_elevation,
        rightFactor_eq_neg_left, neg_mul])

theorem hasDerivAt_rightDerivative (n : ℕ) (j : ℤ) (q : ℝ) :
    HasDerivAt (rightDerivative n j) (rightSecond n j q) q := by
  exact (hasDerivAt_leftDerivative n (j + 1) q).neg

theorem abs_leftSecond_le (n : ℕ) (j : ℤ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |leftSecond n j q| ≤ 2 * ((n + 1 : ℕ) : ℝ) * n := by
  unfold leftSecond
  by_cases hj : 0 ≤ j ∧ j ≤ (n + 1 : ℕ)
  · rw [abs_mul]
    calc
      |leftFactor n j| * |massSecond (n + 1) j q| ≤
          1 * |massSecond (n + 1) j q| :=
        mul_le_mul_of_nonneg_right (abs_leftFactor_le_one n j hj.1 hj.2) (abs_nonneg _)
      _ ≤ 2 * ((n + 1 : ℕ) : ℝ) * n := by
        simpa using abs_massSecond_le (n + 1) j hq0 hq1
  · rw [massSecond_eq_zero_of_outside (n + 1) j hj q]
    simp only [mul_zero, abs_zero]
    positivity

theorem abs_rightSecond_le (n : ℕ) (j : ℤ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |rightSecond n j q| ≤ 2 * ((n + 1 : ℕ) : ℝ) * n := by
  simpa only [rightSecond, abs_neg] using abs_leftSecond_le n (j + 1) hq0 hq1

#print axioms mass_elevate_q
#print axioms mass_elevate_complement
#print axioms left_degree_elevation
#print axioms right_degree_elevation
#print axioms hasDerivAt_left
#print axioms hasDerivAt_right
#print axioms abs_leftSecond_le
#print axioms abs_rightSecond_le

end ForestUnimodality.BinomialParameterDerivative
