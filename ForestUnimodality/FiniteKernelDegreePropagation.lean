import ForestUnimodality.FiniteKernelInterpolation

/-! Degree propagation for binomial residuals with no fixed-index charge.
The recurrence preserves every integer index, including outside the support. -/
namespace ForestUnimodality

theorem binomialMass_succ_convolution (n : ℕ) (j : ℤ) (q : ℝ) :
    binomialMass (n + 1) j q =
      (1 - q) * binomialMass n j q + q * binomialMass n (j - 1) q := by
  apply (mul_left_cancel₀ (show ((n + 1 : ℕ) : ℝ) ≠ 0 by positivity))
  linear_combination
    -(BinomialParameterDerivative.mass_elevate_q n j q) -
      (BinomialParameterDerivative.mass_elevate_complement n j q)

theorem binomialKernel_succ_convolution (n : ℕ) (j : ℤ) (q wL wR wC : ℝ) :
    binomialKernel (n + 1) j q wL wR wC =
      (1 - q) * binomialKernel n j q wL wR wC +
        q * binomialKernel n (j - 1) q wL wR wC := by
  simp only [binomialKernel, binomialMass_succ_convolution]
  rw [show j + 1 - 1 = j by omega, show j - 1 + 1 = j by omega]
  ring

namespace FiniteKernelInterpolation
open Finset

noncomputable def Row.degreeIncrement {ι : Type*} (r : Row ι) (n : ℕ) (q : ℝ) : ℝ :=
  r.dM * (2 * (n : ℝ) + 1) - r.B - r.dδ * q * (1 - q) -
    ∑ i ∈ r.terms, r.price i * q * (1 - r.retention i) * transform n (r.retention i) q

theorem Row.residual_succ_convolution {ι : Type*} (r : Row ι)
    (hf : ∀ j, r.fixedPrice j = 0) (n : ℕ) (j : ℤ) (q : ℝ) :
    r.residual (n + 1) j q = (1 - q) * r.residual n j q +
      q * r.residual n (j - 1) q + r.degreeIncrement n q := by
  have hs : (∑ i ∈ r.terms, r.price i * transform (n + 1) (r.retention i) q) =
      (∑ i ∈ r.terms, r.price i * transform n (r.retention i) q) -
        ∑ i ∈ r.terms, r.price i * q * (1 - r.retention i) * transform n (r.retention i) q := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    simp only [transform, pow_succ]
    ring
  simp only [Row.residual, hf, zero_mul, add_zero, Row.quadratic, Row.degreeIncrement,
    Nat.cast_add, Nat.cast_one, Int.cast_sub, Int.cast_one]
  rw [binomialKernel_succ_convolution, hs]
  ring

theorem Row.residual_nonneg_from_degree {ι : Type*} (r : Row ι)
    (hf : ∀ j, r.fixedPrice j = 0) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (N : ℕ) (hbase : ∀ j : ℤ, 0 ≤ r.residual N j q)
    (hinc : ∀ n, N ≤ n → 0 ≤ r.degreeIncrement n q) :
    ∀ n, N ≤ n → ∀ j : ℤ, 0 ≤ r.residual n j q := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
    intro j
    rw [r.residual_succ_convolution hf]
    exact add_nonneg
      (add_nonneg (mul_nonneg (sub_nonneg.mpr hq.2) (ih j))
        (mul_nonneg hq.1 (ih (j - 1)))) (hinc n hn)

#print axioms ForestUnimodality.binomialMass_succ_convolution
#print axioms ForestUnimodality.binomialKernel_succ_convolution
#print axioms Row.residual_succ_convolution
#print axioms Row.residual_nonneg_from_degree
end FiniteKernelInterpolation
end ForestUnimodality
