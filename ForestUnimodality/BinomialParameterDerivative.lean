import ForestUnimodality.BinomialGradientIdentity
import ForestUnimodality.ReciprocalGradientBudget
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Derivatives with respect to the actual Bernoulli parameter, at every
integer index including the support boundary. The degree is never treated as
a real parameter. These identities support the continuous finite certificates. -/
namespace ForestUnimodality.BinomialParameterDerivative

open Polynomial

noncomputable def massPolynomial (n : ℕ) (j : ℤ) : Polynomial ℝ :=
  if 0 ≤ j then bernsteinPolynomial ℝ n j.toNat else 0

theorem eval_massPolynomial (n : ℕ) (j : ℤ) (q : ℝ) :
    (massPolynomial n j).eval q = binomialMass n j q := by
  by_cases hj : 0 ≤ j
  · lift j to ℕ using hj
    simp [massPolynomial, bernsteinPolynomial, binomialMass_nat]
  · simp [massPolynomial, hj, binomialMass_eq_zero_of_neg n (lt_of_not_ge hj)]

theorem derivative_massPolynomial (n : ℕ) (j : ℤ) :
    (massPolynomial n j).derivative =
      C (n : ℝ) * (massPolynomial (n - 1) (j - 1) - massPolynomial (n - 1) j) := by
  by_cases hj : 0 ≤ j
  · lift j to ℕ using hj
    cases j with
    | zero =>
      simp [massPolynomial, bernsteinPolynomial.derivative_zero]
    | succ j =>
      have he : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
      rw [he]
      have hj : (0 : ℤ) ≤ (j : ℤ) + 1 := by omega
      simp [massPolynomial, hj, bernsteinPolynomial.derivative_succ]
  · have hp : ¬ 0 ≤ j - 1 := by omega
    simp only [massPolynomial, if_neg hj, if_neg hp, derivative_zero, sub_self, mul_zero]

/-- The first derivative is an adjacent finite difference of a genuine
lower-degree binomial law; it remains valid at q=0 and q=1. -/
theorem hasDerivAt_mass (n : ℕ) (j : ℤ) (q : ℝ) :
    HasDerivAt (binomialMass n j)
      ((n : ℝ) * (binomialMass (n - 1) (j - 1) q - binomialMass (n - 1) j q)) q := by
  have h := (massPolynomial n j).hasDerivAt q
  simpa only [derivative_massPolynomial, eval_mul, eval_C, eval_sub,
    eval_massPolynomial] using h

noncomputable def massDerivative (n : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  (n : ℝ) * (binomialMass (n - 1) (j - 1) q - binomialMass (n - 1) j q)

noncomputable def massSecond (n : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  (n : ℝ) * (n - 1 : ℕ) * (binomialMass (n - 2) (j - 2) q -
    2 * binomialMass (n - 2) (j - 1) q + binomialMass (n - 2) j q)

theorem hasDerivAt_massDerivative (n : ℕ) (j : ℤ) (q : ℝ) :
    HasDerivAt (massDerivative n j) (massSecond n j q) q := by
  have h := ((hasDerivAt_mass (n - 1) (j - 1) q).sub
    (hasDerivAt_mass (n - 1) j q)).const_mul (n : ℝ)
  change HasDerivAt (massDerivative n j) _ q at h
  convert h using 1
  unfold massSecond
  rw [show n - 1 - 1 = n - 2 by omega, show j - 1 - 1 = j - 2 by omega]
  ring

theorem continuous_mass (n : ℕ) (j : ℤ) : Continuous (binomialMass n j) :=
  continuous_iff_continuousAt.mpr fun q => (hasDerivAt_mass n j q).continuousAt

theorem deriv_mass (n : ℕ) (j : ℤ) (q : ℝ) :
    deriv (binomialMass n j) q = massDerivative n j q :=
  (hasDerivAt_mass n j q).deriv

theorem deriv_massDerivative (n : ℕ) (j : ℤ) (q : ℝ) :
    deriv (massDerivative n j) q = massSecond n j q :=
  (hasDerivAt_massDerivative n j q).deriv

/-- A finite set of distinct integer atoms has total mass at most one,
including indices outside the support. -/
theorem sum_mass_le_one (n : ℕ) (s : Finset ℤ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∑ j ∈ s, binomialMass n j q ≤ 1 := by
  let t : Finset ℤ := (Finset.range (n + 1)).map
    ⟨Int.ofNat, Int.ofNat_injective⟩
  have hz (j : ℤ) (hj : j ∉ t) : binomialMass n j q = 0 := by
    by_cases hs : 0 ≤ j ∧ j ≤ n
    · exfalso
      apply hj
      exact Finset.mem_map.mpr ⟨j.toNat, Finset.mem_range.mpr (by omega),
        Int.toNat_of_nonneg hs.1⟩
    · simp [binomialMass, hs]
  calc
    ∑ j ∈ s, binomialMass n j q = ∑ j ∈ s ∩ t, binomialMass n j q := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro j hjs hjst
      exact hz j (by simpa only [Finset.mem_inter, hjs, true_and] using hjst)
    _ ≤ ∑ j ∈ t, binomialMass n j q :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun j _ _ => binomialMass_nonneg n j hq0 hq1)
    _ = 1 := by
      simp only [t, Finset.sum_map, Function.Embedding.coeFn_mk]
      exact ReciprocalGradientBudget.sum_binomialMass n q

theorem abs_three_difference_le_two (n : ℕ) (j : ℤ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |binomialMass n (j - 2) q - 2 * binomialMass n (j - 1) q +
      binomialMass n j q| ≤ 2 := by
  have hs := sum_mass_le_one n {j - 2, j - 1, j} hq0 hq1
  rw [Finset.sum_insert (show j - 2 ∉ ({j - 1, j} : Finset ℤ) by simp),
    Finset.sum_pair (show j - 1 ≠ j by omega)] at hs
  have h0 := binomialMass_nonneg n (j - 2) hq0 hq1
  have h1 := binomialMass_nonneg n (j - 1) hq0 hq1
  have h2 := binomialMass_nonneg n j hq0 hq1
  apply abs_le.mpr
  constructor <;> linarith

/-- The sharp coefficient bound for the second parameter derivative. -/
theorem abs_massSecond_le (n : ℕ) (j : ℤ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |massSecond n j q| ≤ 2 * (n : ℝ) * (n - 1 : ℕ) := by
  have h := abs_three_difference_le_two (n - 2) j hq0 hq1
  unfold massSecond
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg n),
    abs_of_nonneg (Nat.cast_nonneg (n - 1))]
  nlinarith [mul_le_mul_of_nonneg_left h
    (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg (n - 1)))]

noncomputable def centralDerivative (n : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  2 * massDerivative n j q - massDerivative n (j - 1) q - massDerivative n (j + 1) q

noncomputable def centralSecond (n : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  (n : ℝ) * (n - 1 : ℕ) * (-binomialMass (n - 2) (j - 3) q +
    4 * binomialMass (n - 2) (j - 2) q - 6 * binomialMass (n - 2) (j - 1) q +
    4 * binomialMass (n - 2) j q - binomialMass (n - 2) (j + 1) q)

theorem hasDerivAt_central (n : ℕ) (j : ℤ) (q : ℝ) :
    HasDerivAt (fun x => binomialKernel n j x 0 0 1) (centralDerivative n j q) q := by
  have h := (((hasDerivAt_mass n j q).const_mul 2).sub
    (hasDerivAt_mass n (j - 1) q)).sub (hasDerivAt_mass n (j + 1) q)
  convert h using 1 <;> first
    | rfl
    | (ext x; simp [binomialKernel])

theorem hasDerivAt_centralDerivative (n : ℕ) (j : ℤ) (q : ℝ) :
    HasDerivAt (centralDerivative n j) (centralSecond n j q) q := by
  have h := (((hasDerivAt_massDerivative n j q).const_mul 2).sub
    (hasDerivAt_massDerivative n (j - 1) q)).sub
    (hasDerivAt_massDerivative n (j + 1) q)
  change HasDerivAt (centralDerivative n j) _ q at h
  convert h using 1
  simp only [centralSecond, massSecond,
    show j - 1 - 2 = j - 3 by omega,
    show j - 1 - 1 = j - 2 by omega,
    show j + 1 - 2 = j - 1 by omega,
    show j + 1 - 1 = j by omega]
  ring

theorem abs_five_difference_le_six (n : ℕ) (j : ℤ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |-binomialMass n (j - 3) q + 4 * binomialMass n (j - 2) q -
      6 * binomialMass n (j - 1) q + 4 * binomialMass n j q -
      binomialMass n (j + 1) q| ≤ 6 := by
  have hs := sum_mass_le_one n {j - 3, j - 2, j - 1, j, j + 1} hq0 hq1
  rw [Finset.sum_insert (show j - 3 ∉ ({j - 2, j - 1, j, j + 1} : Finset ℤ) by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (show j - 2 ∉ ({j - 1, j, j + 1} : Finset ℤ) by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (show j - 1 ∉ ({j, j + 1} : Finset ℤ) by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_pair (show j ≠ j + 1 by omega)] at hs
  have h0 := binomialMass_nonneg n (j - 3) hq0 hq1
  have h1 := binomialMass_nonneg n (j - 2) hq0 hq1
  have h2 := binomialMass_nonneg n (j - 1) hq0 hq1
  have h3 := binomialMass_nonneg n j hq0 hq1
  have h4 := binomialMass_nonneg n (j + 1) hq0 hq1
  apply abs_le.mpr
  constructor <;> linarith

/-- The actual central kernel has the five-point coefficient vector
(-1,4,-6,4,-1), hence the uniform bound 6 n(n-1). -/
theorem abs_centralSecond_le (n : ℕ) (j : ℤ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |centralSecond n j q| ≤ 6 * (n : ℝ) * (n - 1 : ℕ) := by
  have h := abs_five_difference_le_six (n - 2) j hq0 hq1
  unfold centralSecond
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg n),
    abs_of_nonneg (Nat.cast_nonneg (n - 1))]
  nlinarith [mul_le_mul_of_nonneg_left h
    (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg (n - 1)))]

#print axioms derivative_massPolynomial
#print axioms hasDerivAt_mass
#print axioms hasDerivAt_massDerivative
#print axioms abs_massSecond_le
#print axioms hasDerivAt_central
#print axioms hasDerivAt_centralDerivative
#print axioms abs_centralSecond_le

end ForestUnimodality.BinomialParameterDerivative
