import Mathlib.Algebra.Polynomial.Coeff

/-!
Guarded binomial coefficients for the blocks `X^j * (1 + X)^m`.

The guard is essential: natural-number subtraction alone would turn a
negative lower binomial index into zero and return `m.choose 0 = 1`.
This module connects the arithmetic formula to actual polynomial coefficients.
It makes no assertion about which polynomials arise from forests.
-/

namespace ForestUnimodality

/-- `C(m, k - j)`, with the value zero when the lower index would be negative. -/
def shiftedChoose (m j k : ℕ) : ℕ :=
  if j ≤ k then m.choose (k - j) else 0

@[simp] theorem shiftedChoose_of_lt (m : ℕ) {j k : ℕ} (h : k < j) :
    shiftedChoose m j k = 0 := by
  simp [shiftedChoose, Nat.not_le_of_lt h]

theorem shiftedChoose_of_le (m : ℕ) {j k : ℕ} (h : j ≤ k) :
    shiftedChoose m j k = m.choose (k - j) := by
  simp [shiftedChoose, h]

@[simp] theorem shiftedChoose_zero_shift (m k : ℕ) :
    shiftedChoose m 0 k = m.choose k := by
  simp [shiftedChoose]

@[simp] theorem shiftedChoose_self (m j : ℕ) :
    shiftedChoose m j j = 1 := by
  simp [shiftedChoose]

/-- A shifted block has no terms above degree `m + j`. -/
theorem shiftedChoose_eq_zero_of_gt {m j k : ℕ} (h : m + j < k) :
    shiftedChoose m j k = 0 := by
  have hjk : j ≤ k := by omega
  rw [shiftedChoose_of_le m hjk]
  apply Nat.choose_eq_zero_of_lt
  omega

/-- Shifting the block and the coefficient index together leaves the value unchanged. -/
@[simp] theorem shiftedChoose_succ_succ (m j k : ℕ) :
    shiftedChoose m (j + 1) (k + 1) = shiftedChoose m j k := by
  simp [shiftedChoose]

/-- The guarded binomial formula is the coefficient of the actual shifted block,
over any coefficient semiring (in particular over `ℕ` or `ℤ`). -/
theorem coeff_shifted_binomial (R : Type*) [Semiring R] (m j k : ℕ) :
    ((Polynomial.X : Polynomial R) ^ j * (1 + Polynomial.X) ^ m).coeff k =
      (shiftedChoose m j k : R) := by
  rw [Polynomial.coeff_X_pow_mul', Polynomial.coeff_one_add_X_pow]
  by_cases h : j ≤ k <;> simp [shiftedChoose, h]

/-- The signed adjacent difference uses a shifted guard on the previous term.
This matches `C(m, k+1-j) - C(m, k-j)` without truncated-index errors. -/
theorem coeff_shifted_binomial_difference (m j k : ℕ) :
    ((Polynomial.X : Polynomial ℤ) ^ j * (1 + Polynomial.X) ^ m).coeff (k + 1) -
        ((Polynomial.X : Polynomial ℤ) ^ j * (1 + Polynomial.X) ^ m).coeff k =
      (shiftedChoose m j (k + 1) : ℤ) -
        (shiftedChoose m (j + 1) (k + 1) : ℤ) := by
  rw [coeff_shifted_binomial, coeff_shifted_binomial, shiftedChoose_succ_succ]

#print axioms coeff_shifted_binomial
#print axioms coeff_shifted_binomial_difference

end ForestUnimodality
