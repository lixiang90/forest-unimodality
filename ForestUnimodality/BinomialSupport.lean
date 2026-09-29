import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Discrete supporting lines for binomial coefficients. The slope is the
Pascal increment, so no continuous convexity assertion is needed. -/

namespace ForestUnimodality

/-- Summing increasing Pascal increments gives a lower bound from the first. -/
theorem choose_add_ge_first_increment (n t r : ℕ) (hr : 1 ≤ r) :
    n.choose r + t * n.choose (r - 1) ≤ (n + t).choose r := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hmono := Nat.choose_le_choose (r - 1) (Nat.le_add_right n t)
    change n.choose r + (t + 1) * n.choose (r - 1) ≤ (n + t + 1).choose r
    rw [Nat.choose_succ_left _ _ hr]
    nlinarith

/-- Summing increasing Pascal increments bounds the sum by the last. -/
theorem choose_add_le_last_increment (n t r : ℕ) (hr : 1 ≤ r) :
    (n + t).choose r ≤ n.choose r + t * (n + t).choose (r - 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hmono := Nat.choose_le_choose (r - 1) (Nat.le_succ (n + t))
    have hprod := Nat.mul_le_mul_left t hmono
    rw [Nat.add_succ, Nat.succ_eq_add_one, Nat.choose_succ_left _ _ hr]
    nlinarith

/-- The line through the values at n and n+1 supports all integer values. -/
theorem choose_support_line (n m r : ℕ) (hr : 1 ≤ r) :
    (n.choose r : ℝ) + ((m : ℝ) - (n : ℝ)) * (n.choose (r - 1) : ℝ) ≤
      (m.choose r : ℝ) := by
  rcases le_total n m with hnm | hmn
  · have h := choose_add_ge_first_increment n (m - n) r hr
    rw [Nat.add_sub_of_le hnm] at h
    have hc : (n.choose r : ℝ) + ((m - n : ℕ) : ℝ) *
        (n.choose (r - 1) : ℝ) ≤ (m.choose r : ℝ) := by exact_mod_cast h
    simpa only [Nat.cast_sub hnm] using hc
  · have h := choose_add_le_last_increment m (n - m) r hr
    rw [Nat.add_sub_of_le hmn] at h
    have hc : (n.choose r : ℝ) ≤ (m.choose r : ℝ) +
        ((n - m : ℕ) : ℝ) * (n.choose (r - 1) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub hmn] at hc
    nlinarith

/-- The precise support line used in the finite-certificate mean inequality. -/
theorem choose_complement_support_line (v r d : ℕ)
    (hv : 2 ≤ v) (hr : 2 ≤ r) (hd : d ≤ v) :
    ((v - 2).choose r : ℝ) + (2 - (d : ℝ)) * ((v - 2).choose (r - 1) : ℝ) ≤
      ((v - d).choose r : ℝ) := by
  have h := choose_support_line (v - 2) (v - d) r (by omega)
  rw [Nat.cast_sub hd, Nat.cast_sub hv, Nat.cast_ofNat] at h
  convert h using 1
  ring

#print axioms choose_add_ge_first_increment
#print axioms choose_add_le_last_increment
#print axioms choose_support_line
#print axioms choose_complement_support_line

end ForestUnimodality
