import ForestUnimodality.ReferenceRankLogConcavity
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination

/-! The matching-reference sequence decreases after the floor of its
Bernoulli mean plus one. A polynomial differential identity and the already
proved log-concavity give the exact integral cutoff. -/

namespace ForestUnimodality

open Polynomial

private theorem mul_derivative_pow (P : Polynomial ℝ) (n : ℕ) :
    P * derivative (P ^ n) = (n : Polynomial ℝ) * P ^ n * derivative P := by
  cases n with
  | zero => simp
  | succ n =>
    rw [derivative_pow_succ]
    simp only [map_add, map_one, map_natCast, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

private theorem two_weight_product_differential (s v : ℕ) :
    (1 + 3 * X + 2 * X ^ 2) * derivative ((1 + 2 * X) ^ v * (1 + X) ^ s) =
      (((s : Polynomial ℝ) + 2 * (v : Polynomial ℝ)) +
        2 * ((s : Polynomial ℝ) + (v : Polynomial ℝ)) * X) *
        ((1 + 2 * X) ^ v * (1 + X) ^ s) := by
  have hA := mul_derivative_pow (1 + 2 * X : Polynomial ℝ) v
  have hB := mul_derivative_pow (1 + X : Polynomial ℝ) s
  norm_num only [derivative_add, derivative_one, derivative_mul,
    derivative_ofNat, derivative_X, zero_mul, zero_add, mul_one] at hA hB
  rw [derivative_mul]
  calc
    _ = ((1 + 2 * X) * derivative ((1 + 2 * X) ^ v)) *
        (1 + X) * (1 + X) ^ s +
      ((1 + X) * derivative ((1 + X) ^ s)) *
        (1 + 2 * X) * (1 + 2 * X) ^ v := by ring
    _ = _ := by rw [hA, hB]; ring

private theorem coeff_X_derivative (P : Polynomial ℝ) (k : ℕ) :
    (X * derivative P).coeff k = (k : ℝ) * P.coeff k := by
  cases k with
  | zero => simp
  | succ k => rw [coeff_X_mul, coeff_derivative]; push_cast; ring

/-- The exact three-term recurrence, with subtraction in the real field. -/
theorem matchingUpperCount_recurrence (a v k : ℕ) (hva : v ≤ a) :
    ((k : ℝ) + 2) * (matchingUpperCount a v (k + 2) : ℝ) =
      ((a : ℝ) + v - 3 * (k + 1)) * (matchingUpperCount a v (k + 1) : ℝ) +
      2 * ((a : ℝ) - k) * (matchingUpperCount a v k : ℝ) := by
  let P : Polynomial ℝ := (1 + 2 * X) ^ v * (1 + X) ^ (a - v)
  have h := two_weight_product_differential (a - v) v
  have hdiff : derivative P + 3 * (X * derivative P) +
      2 * (X * (X * derivative P)) =
      ((a : Polynomial ℝ) + (v : Polynomial ℝ)) * P +
        (2 * (a : Polynomial ℝ)) * (X * P) := by
    have hcast : ((a - v : ℕ) : Polynomial ℝ) =
        (a : Polynomial ℝ) - (v : Polynomial ℝ) := by
      exact Nat.cast_sub hva
    dsimp only [P]
    rw [hcast] at h
    linear_combination h
  have hc := congrArg (fun Q : Polynomial ℝ => Q.coeff (k + 1)) hdiff
  simp only [coeff_add, coeff_ofNat_mul, coeff_X_mul, coeff_derivative,
    coeff_X_derivative] at hc
  have hrhs : (((a : Polynomial ℝ) + (v : Polynomial ℝ)) * P).coeff (k + 1) =
      ((a : ℝ) + v) * P.coeff (k + 1) := by
    rw [add_mul, coeff_add, coeff_natCast_mul, coeff_natCast_mul]
    ring
  rw [hrhs] at hc
  have htwo : (2 * (a : Polynomial ℝ) * (X * P)).coeff (k + 1) =
      2 * (a : ℝ) * P.coeff k := by
    rw [mul_assoc, coeff_ofNat_mul, coeff_natCast_mul, coeff_X_mul]
    ring
  rw [htwo] at hc
  have hcoeff (j : ℕ) : P.coeff j = (matchingUpperCount a v j : ℝ) :=
    coeff_matching_polynomial_real a v j
  simp only [hcoeff, Nat.cast_add, Nat.cast_one] at hc
  linear_combination hc

theorem matchingUpperCount_eq_zero_of_card_lt (a v k : ℕ) (hva : v ≤ a)
    (hak : a < k) : matchingUpperCount a v k = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  exact (Nat.not_le_of_lt hak) ((matchingUpperCount_pos_iff a v k hva).mp hp)

/-- A positive step would force `6*k < 3*a+v+1`. Since the parameters
are integers, every step strictly beyond the reference mean is decreasing. -/
theorem matchingUpperCount_succ_le_of_mean_lt (a v k : ℕ) (hva : v ≤ a)
    (hmean : 3 * a + v < 6 * k) :
    matchingUpperCount a v (k + 1) ≤ matchingUpperCount a v k := by
  by_cases hak : a < k
  · rw [matchingUpperCount_eq_zero_of_card_lt a v (k + 1) hva (by omega)]
    exact Nat.zero_le _
  have hka : k ≤ a := by omega
  have hk0 : 0 < k := by omega
  cases k with
  | zero => omega
  | succ k =>
    change matchingUpperCount a v (k + 2) ≤ matchingUpperCount a v (k + 1)
    by_contra hnot
    have hup : (matchingUpperCount a v (k + 1) : ℝ) <
        (matchingUpperCount a v (k + 2) : ℝ) := by exact_mod_cast (Nat.lt_of_not_ge hnot)
    have hpos : (0 : ℝ) < (matchingUpperCount a v (k + 1) : ℝ) := by
      exact_mod_cast (matchingUpperCount_pos_iff a v (k + 1) hva).mpr hka
    have hnonneg : (0 : ℝ) ≤ (matchingUpperCount a v k : ℝ) := by positivity
    have hlog : (matchingUpperCount a v k : ℝ) *
        (matchingUpperCount a v (k + 2) : ℝ) ≤
        (matchingUpperCount a v (k + 1) : ℝ) ^ 2 := by
      exact_mod_cast matchingUpperCount_log_concave a v k
    have hprev : (matchingUpperCount a v k : ℝ) ≤
        (matchingUpperCount a v (k + 1) : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hup.le hnonneg
      apply (mul_le_mul_iff_left₀ hpos).mp
      nlinarith
    have hac : (k : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show k ≤ a by omega)
    have hstep := matchingUpperCount_recurrence a v k hva
    have hprev' := mul_le_mul_of_nonneg_left hprev
      (show (0 : ℝ) ≤ 2 * ((a : ℝ) - k) by linarith)
    have hbound : ((k : ℝ) + 2) * (matchingUpperCount a v (k + 2) : ℝ) ≤
        ((a : ℝ) + v - 3 * (k + 1) + 2 * ((a : ℝ) - k)) *
          (matchingUpperCount a v (k + 1) : ℝ) := by nlinarith
    have hmean' : 3 * (a : ℝ) + v + 1 ≤ 6 * ((k : ℝ) + 1) := by
      exact_mod_cast (show 3 * a + v + 1 ≤ 6 * (k + 1) by omega)
    have hfac : (a : ℝ) + v - 3 * (k + 1) + 2 * ((a : ℝ) - k) ≤ k + 2 :=
      by linarith
    have hfac' := mul_le_mul_of_nonneg_right hfac hpos.le
    have hup' := mul_lt_mul_of_pos_left hup (show (0 : ℝ) < k + 2 by positivity)
    linarith

/-- The explicit cutoff used in the analytic window, including degrees
beyond the full support. -/
theorem matchingUpperCount_tail (a v k : ℕ) (hva : v ≤ a)
    (hk : (3 * a + v) / 6 + 1 ≤ k) :
    matchingUpperCount a v (k + 1) ≤ matchingUpperCount a v k := by
  exact matchingUpperCount_succ_le_of_mean_lt a v k hva (by omega)

#print axioms matchingUpperCount_recurrence
#print axioms matchingUpperCount_tail

end ForestUnimodality
