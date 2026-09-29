import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic

/-! Effective upper Stirling error at every positive natural. Robbins' proved
stepwise estimate is telescoped through a monotone compensated sequence. -/
namespace ForestUnimodality.FiniteStirling
open Real Filter
open scoped Topology

theorem log_stirlingSeq_upper {n : ℕ} (hn : n ≠ 0) :
    Real.log (Stirling.stirlingSeq n) ≤ Real.log (Real.sqrt Real.pi) + 1 / (12 * n) := by
  let f : ℕ → ℝ := fun k => Real.log (Stirling.stirlingSeq (k + 1)) - 1 / (12 * (k + 1))
  have hmono : Monotone f := by
    apply monotone_nat_of_le_succ
    intro k
    have he := Stirling.log_stirlingSeq_sdiff_le (k + 1)
    have hid : (1 : ℝ) / (12 * (k + 1)) - 1 / (12 * (k + 2)) =
        1 / (12 * (k + 1) * (k + 2)) := by
      field_simp
      ring
    dsimp [f]
    push_cast at he ⊢
    rw [show (k : ℝ) + 1 + 1 = k + 2 by ring] at he ⊢
    rw [← hid] at he
    linarith
  have hlog : Tendsto (fun k : ℕ => Real.log (Stirling.stirlingSeq (k + 1)))
      atTop (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))).tendsto.comp
      (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1))
  have hinv : Tendsto (fun k : ℕ => (1 : ℝ) / (12 * (k + 1))) atTop (𝓝 0) := by
    have he := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 12 : ℝ)
    convert he using 1
    · funext k
      field_simp
    · simp
  have hlim : Tendsto f atTop (𝓝 (Real.log (Real.sqrt Real.pi))) := by
    simpa only [sub_zero] using hlog.sub hinv
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have he := hmono.ge_of_tendsto hlim k
  dsimp [f] at he
  push_cast
  linarith

theorem stirlingSeq_upper {n : ℕ} (hn : n ≠ 0) :
    Stirling.stirlingSeq n ≤ Real.sqrt Real.pi * Real.exp (1 / (12 * n)) := by
  have hpos : 0 < Stirling.stirlingSeq n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact Stirling.stirlingSeq'_pos k
  have he := Real.exp_le_exp.mpr (log_stirlingSeq_upper hn)
  rwa [Real.exp_log hpos, Real.exp_add,
    Real.exp_log (Real.sqrt_pos.mpr Real.pi_pos)] at he

theorem factorial_upper {n : ℕ} (hn : n ≠ 0) :
    (n.factorial : ℝ) ≤ Real.sqrt (2 * Real.pi * n) *
      ((n : ℝ) / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he := stirlingSeq_upper hn
  rw [Stirling.stirlingSeq, div_le_iff₀ (by positivity)] at he
  convert! he using 1
  rw [show 2 * Real.pi * (n : ℝ) = Real.pi * (2 * n) by ring,
    Real.sqrt_mul Real.pi_pos.le]
  ring

theorem factorial_two_sided {n : ℕ} (hn : n ≠ 0) :
    Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) ∧
      (n.factorial : ℝ) ≤ Real.sqrt (2 * Real.pi * n) *
        ((n : ℝ) / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) :=
  ⟨Stirling.le_factorial_stirling n, factorial_upper hn⟩

#print axioms log_stirlingSeq_upper
#print axioms factorial_two_sided
end ForestUnimodality.FiniteStirling
