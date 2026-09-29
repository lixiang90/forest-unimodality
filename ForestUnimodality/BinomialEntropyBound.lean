import ForestUnimodality.BinomialGradientIdentity
import ForestUnimodality.BernoulliEntropy

/-! Finite Stirling control of actual binomial masses through relative entropy. -/
namespace ForestUnimodality.BinomialEntropyBound
open Real

theorem log_factorial_upper {n : ℕ} (hn : n ≠ 0) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + Real.log n / 2 +
      Real.log (2 * Real.pi) / 2 + 1 / (12 * n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he := FiniteStirling.log_stirlingSeq_upper hn
  rw [Stirling.log_stirlingSeq_formula, Real.log_sqrt Real.pi_pos.le,
    Real.log_div hnR.ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR.ne'] at he
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  linarith

theorem binomialMass_pos (n k : ℕ) (hk : k ≤ n) {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    0 < binomialMass n k q := by
  rw [binomialMass_nat]
  have hc : 0 < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  exact mul_pos (mul_pos hc (pow_pos hq.1 _)) (pow_pos (sub_pos.mpr hq.2) _)

theorem log_binomialMass_stirling (n k : ℕ) (hk0 : 0 < k) (hkn : k < n)
    {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    Real.log (binomialMass n k q) ≤
      (n : ℝ) * Real.log n - (k : ℝ) * Real.log k - (n - k : ℕ) * Real.log (n - k : ℕ) +
      (k : ℝ) * Real.log q + (n - k : ℕ) * Real.log (1 - q) +
      (Real.log n - Real.log k - Real.log (n - k : ℕ) - Real.log (2 * Real.pi)) / 2 +
      1 / (12 * n) := by
  have hn0 : n ≠ 0 := by omega
  have hl0 : n - k ≠ 0 := by omega
  have hc : 0 < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hkn.le
  have hkF : 0 < (k.factorial : ℝ) := by positivity
  have hlF : 0 < ((n - k).factorial : ℝ) := by positivity
  have hchoose : (n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn.le
  have hclog := congrArg Real.log hchoose
  rw [Real.log_mul (mul_pos hc hkF).ne' hlF.ne', Real.log_mul hc.ne' hkF.ne'] at hclog
  have hu := log_factorial_upper hn0
  have hkL := Stirling.le_log_factorial_stirling hk0.ne'
  have hlL := Stirling.le_log_factorial_stirling hl0
  have hsum : (n : ℝ) = (k : ℝ) + (n - k : ℕ) := by
    exact_mod_cast (show n = k + (n - k) by omega)
  rw [binomialMass_nat, Real.log_mul (mul_pos hc (pow_pos hq.1 _)).ne'
      (pow_pos (sub_pos.mpr hq.2) _).ne',
    Real.log_mul hc.ne' (pow_pos hq.1 _).ne', Real.log_pow, Real.log_pow]
  linarith

theorem entropy_identity {N K L q : ℝ} (hN : 0 < N) (hK : 0 < K) (hL : 0 < L)
    (hs : N = K + L) :
    N * Real.log N - K * Real.log K - L * Real.log L +
      K * Real.log q + L * Real.log (1 - q) =
        -N * BernoulliEntropy.divergence q (K / N) := by
  have hcomp : 1 - K / N = L / N := by field_simp; linarith
  unfold BernoulliEntropy.divergence
  rw [hcomp, Real.log_div hK.ne' hN.ne', Real.log_div hL.ne' hN.ne']
  field_simp
  linear_combination Real.log N * hs

theorem log_binomialMass_entropy (n k : ℕ) (hk0 : 0 < k) (hkn : k < n)
    {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    Real.log (binomialMass n k q) ≤
      -(n : ℝ) * BernoulliEntropy.divergence q ((k : ℝ) / n) -
        Real.log (2 * Real.pi * (k : ℝ) * (n - k : ℕ) / n) / 2 + 1 / (12 * n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have hlR : 0 < ((n - k : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - k by omega)
  have hsum : (n : ℝ) = (k : ℝ) + (n - k : ℕ) := by
    exact_mod_cast (show n = k + (n - k) by omega)
  have he := log_binomialMass_stirling n k hk0 hkn hq
  have hid := entropy_identity (q := q) hnR hkR hlR hsum
  have hlog : Real.log (2 * Real.pi * (k : ℝ) * (n - k : ℕ) / n) =
      Real.log (2 * Real.pi) + Real.log k + Real.log (n - k : ℕ) - Real.log n := by
    rw [Real.log_div (by positivity) hnR.ne', Real.log_mul (by positivity) hlR.ne',
      Real.log_mul (by positivity) hkR.ne']
  rw [hlog]
  linarith

theorem binomialMass_entropy_upper (n k : ℕ) (hk0 : 0 < k) (hkn : k < n)
    {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    binomialMass n k q ≤
      Real.exp (-(n : ℝ) * BernoulliEntropy.divergence q ((k : ℝ) / n) + 1 / (12 * n)) /
        Real.sqrt (2 * Real.pi * (k : ℝ) * (n - k : ℕ) / n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have hlR : 0 < ((n - k : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - k by omega)
  have hv : 0 < 2 * Real.pi * (k : ℝ) * (n - k : ℕ) / n := by positivity
  have he := Real.exp_le_exp.mpr (log_binomialMass_entropy n k hk0 hkn hq)
  rw [Real.exp_log (binomialMass_pos n k hkn.le hq)] at he
  refine he.trans_eq ?_
  rw [show -(n : ℝ) * BernoulliEntropy.divergence q ((k : ℝ) / n) -
      Real.log (2 * Real.pi * (k : ℝ) * (n - k : ℕ) / n) / 2 + 1 / (12 * n) =
      (-(n : ℝ) * BernoulliEntropy.divergence q ((k : ℝ) / n) + 1 / (12 * n)) -
        Real.log (Real.sqrt (2 * Real.pi * (k : ℝ) * (n - k : ℕ) / n)) by
      rw [Real.log_sqrt hv.le]; ring,
    Real.exp_sub, Real.exp_log (Real.sqrt_pos.mpr hv)]

#print axioms log_factorial_upper
#print axioms log_binomialMass_entropy
#print axioms binomialMass_entropy_upper
end ForestUnimodality.BinomialEntropyBound
