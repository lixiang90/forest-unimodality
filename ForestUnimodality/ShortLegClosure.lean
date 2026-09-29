import ForestUnimodality.MeanTerminalClosure

/-! Uniform arithmetic closure for arbitrarily many short legs. Identification
of actual path parameters and exhaustive graph reductions remain separate. -/
namespace ForestUnimodality.ShortLegClosure
open Finset

noncomputable def evenBudget (m : ℕ) : ℝ :=
  (5 / 3 : ℝ)^m * (13 * (m : ℝ) / 30 - 89 / 60) - 11 * m / 30 + 89 / 60

noncomputable def oddBudget (m : ℕ) : ℝ :=
  (2 : ℝ)^m * (343 * (m : ℝ) / 1140 - 29 / 60) - 89 * m / 30 + 29 / 60

theorem evenBudget_lower (m : ℕ) (hm : 4 ≤ m) : 788 / 405 ≤ evenBudget m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [evenBudget]
  | succ m hm ih =>
    have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm
    have hp : (1 : ℝ) ≤ (5 / 3 : ℝ)^m := one_le_pow₀ (by norm_num)
    have hc : (8 / 9 : ℝ) ≤
        (2 / 3) * (13 * (m : ℝ) / 30 - 89 / 60) + (5 / 3) * (13 / 30) := by linarith
    have heq : evenBudget (m + 1) - evenBudget m =
        (5 / 3 : ℝ)^m *
          ((2 / 3) * (13 * (m : ℝ) / 30 - 89 / 60) + (5 / 3) * (13 / 30)) - 11 / 30 := by
      simp only [evenBudget, Nat.cast_add, Nat.cast_one, pow_succ]
      ring
    nlinarith

theorem oddBudget_lower (m : ℕ) (hm : 4 ≤ m) : 53 / 380 ≤ oddBudget m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [oddBudget]
  | succ m hm ih =>
    have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm
    have hp : 0 ≤ (2 : ℝ)^m := pow_nonneg (by norm_num) _
    have heq : oddBudget (m + 1) - 2 * oddBudget m =
        (2 : ℝ)^m * (2 * 343 / 1140) + 89 * (m : ℝ) / 30 - 89 / 30 - 29 / 60 := by
      simp only [oddBudget, Nat.cast_add, Nat.cast_one, pow_succ]
      ring
    nlinarith

theorem cluster_lower {ι : Type*} (s : Finset ι) (R a b : ι → ℝ)
    (r h H c A B : ℝ) (hc : 1 ≤ c) (hB : 0 ≤ B)
    (hR : ∀ i ∈ s, c ≤ R i) (ha : ∀ i ∈ s, A ≤ a i)
    (hb : ∀ i ∈ s, -B ≤ b i) (hrlo : 1 ≤ r) (hrhi : r ≤ 3)
    (hh : h ≤ H) (hmain : 0 ≤ A * (s.card : ℝ) - H) :
    c ^ s.card * (A * (s.card : ℝ) - H) - 2 * B * s.card + H ≤
      (∏ i ∈ s, R i) * ((∑ i ∈ s, a i) - h) + (r - 1) * (∑ i ∈ s, b i) + h := by
  have hprod : c ^ s.card ≤ ∏ i ∈ s, R i := by
    simpa only [prod_const] using
      prod_le_prod (fun i (_ : i ∈ s) => (show 0 ≤ c by linarith)) hR
  have hp : 1 ≤ ∏ i ∈ s, R i := (one_le_pow₀ hc).trans hprod
  have hsA : A * (s.card : ℝ) ≤ ∑ i ∈ s, a i := by
    calc
      _ = ∑ _i ∈ s, A := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum ha
  have hsB : -B * (s.card : ℝ) ≤ ∑ i ∈ s, b i := by
    calc
      _ = ∑ _i ∈ s, -B := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum hb
  have hmulA := mul_le_mul_of_nonneg_left hsA (show 0 ≤ ∏ i ∈ s, R i by linarith)
  have hmulP := mul_le_mul_of_nonneg_right hprod hmain
  have hmulH := mul_nonneg (show 0 ≤ (∏ i ∈ s, R i) - 1 by linarith) (sub_nonneg.mpr hh)
  have hmulB := mul_le_mul_of_nonneg_left hsB (show 0 ≤ r - 1 by linarith)
  have hcost := mul_nonneg (show 0 ≤ 3 - r by linarith)
    (mul_nonneg hB (Nat.cast_nonneg (s.card)))
  nlinarith

theorem even_cluster_positive {ι : Type*} (s : Finset ι) (R a b : ι → ℝ)
    (r h : ℝ) (hm : 4 ≤ s.card)
    (hR : ∀ i ∈ s, 5 / 3 ≤ R i) (ha : ∀ i ∈ s, 13 / 30 ≤ a i)
    (hb : ∀ i ∈ s, -(11 / 60) ≤ b i) (hrlo : 1 ≤ r) (hrhi : r ≤ 3)
    (hh : h ≤ 89 / 60) :
    0 < (∏ i ∈ s, R i) * ((∑ i ∈ s, a i) - h) + (r - 1) * (∑ i ∈ s, b i) + h := by
  have hmR : (4 : ℝ) ≤ s.card := by exact_mod_cast hm
  have hl := cluster_lower s R a b r h (89 / 60) (5 / 3) (13 / 30) (11 / 60)
    (by norm_num) (by norm_num) hR ha hb hrlo hrhi hh (by linarith)
  have he := evenBudget_lower s.card hm
  unfold evenBudget at he
  nlinarith

theorem odd_cluster_positive {ι : Type*} (s : Finset ι) (R a b : ι → ℝ)
    (r : ℝ) (hm : 4 ≤ s.card)
    (hR : ∀ i ∈ s, 2 ≤ R i) (ha : ∀ i ∈ s, 343 / 1140 ≤ a i)
    (hb : ∀ i ∈ s, -(89 / 60) ≤ b i) (hrlo : 1 ≤ r) (hrhi : r ≤ 3) :
    0 < (∏ i ∈ s, R i) * ((∑ i ∈ s, a i) - 29 / 60) +
      (r - 1) * (∑ i ∈ s, b i) + 29 / 60 := by
  have hmR : (4 : ℝ) ≤ s.card := by exact_mod_cast hm
  have hl := cluster_lower s R a b r (29 / 60) (29 / 60) 2 (343 / 1140) (89 / 60)
    (by norm_num) (by norm_num) hR ha hb hrlo hrhi (le_refl _) (by linarith)
  have he := oddBudget_lower s.card hm
  unfold oddBudget at he
  nlinarith

#print axioms evenBudget_lower
#print axioms oddBudget_lower
#print axioms even_cluster_positive
#print axioms odd_cluster_positive
end ForestUnimodality.ShortLegClosure
