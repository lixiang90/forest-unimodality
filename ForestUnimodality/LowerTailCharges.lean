import ForestUnimodality.IndependentCountLaplace

/-! Exact finite layer accounting for decreasing bad-event prices. All
cumulative tails are evaluated under one actual hard-core layer law. -/
namespace ForestUnimodality
open Finset

theorem decreasing_prices_telescope (c F : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range (n+1), c i*(F (i+1)-F i)) =
      c n*F (n+1)-c 0*F 0 + ∑ i ∈ range n, (c i-c (i+1))*F (i+1) := by
  induction n with
  | zero => simp [mul_sub]
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

theorem decreasing_prices_le_cumulative (c F bound : ℕ → ℝ) (n : ℕ)
    (hc0 : 0 ≤ c 0) (hcn : 0 ≤ c n)
    (hdecreasing : ∀ i < n, c (i+1) ≤ c i)
    (hF0 : 0 ≤ F 0) (hF : ∀ i ≤ n, F (i+1) ≤ bound (i+1)) :
    (∑ i ∈ range (n+1), c i*(F (i+1)-F i)) ≤
      c n*bound (n+1)+∑ i ∈ range n, (c i-c (i+1))*bound (i+1) := by
  rw [decreasing_prices_telescope]
  have hn := mul_le_mul_of_nonneg_left (hF n le_rfl) hcn
  have hs : (∑ i ∈ range n, (c i-c (i+1))*F (i+1)) ≤
      ∑ i ∈ range n, (c i-c (i+1))*bound (i+1) := by
    apply sum_le_sum
    intro i hi
    have hin := mem_range.mp hi
    exact mul_le_mul_of_nonneg_left (hF i hin.le) (sub_nonneg.mpr (hdecreasing i hin))
  have hstart := mul_nonneg hc0 hF0
  linarith

variable {V : Type*} [DecidableEq V]

noncomputable def hardCoreAvailableSlice (G : SimpleGraph V) (S B : Finset V)
    (z lo hi : ℝ) : ℝ := hardCoreLayerExpectation G S B z
      (fun _ m => if lo ≤ (m : ℝ) ∧ (m : ℝ) < hi then 1 else 0)

theorem hardCoreAvailableLowerTail_nonneg (G : SimpleGraph V) (S B : Finset V)
    {z : ℝ} (hz : 0 ≤ z) (threshold : ℝ) :
    0 ≤ hardCoreAvailableLowerTail G S B z threshold := by
  unfold hardCoreAvailableLowerTail hardCoreLayerExpectation
  apply sum_nonneg
  intro j _
  apply sum_nonneg
  intro m _
  apply mul_nonneg (hardCoreLayerWeight_nonneg G S B hz j m)
  dsimp only
  split_ifs <;> norm_num

/-- The boundary convention is closed at the bottom and open at the top,
exactly matching differences of strict cumulative tails. -/
theorem hardCoreAvailableSlice_eq_tail_sub (G : SimpleGraph V) (S B : Finset V)
    (z : ℝ) {lo hi : ℝ} (hlohi : lo ≤ hi) :
    hardCoreAvailableSlice G S B z lo hi =
      hardCoreAvailableLowerTail G S B z hi - hardCoreAvailableLowerTail G S B z lo := by
  have hp (m : ℕ) : (if lo ≤ (m : ℝ) ∧ (m : ℝ) < hi then (1 : ℝ) else 0) =
      (if (m : ℝ) < hi then 1 else 0) - (if (m : ℝ) < lo then 1 else 0) := by
    by_cases hmlo : lo ≤ (m : ℝ)
    · by_cases hmhi : (m : ℝ) < hi <;> simp [hmlo, hmhi, not_lt.mpr hmlo]
    · have hml : (m : ℝ) < lo := lt_of_not_ge hmlo
      have hmh := hml.trans_le hlohi
      simp [hmlo, hml, hmh]
  simp only [hardCoreAvailableSlice, hardCoreAvailableLowerTail, hardCoreLayerExpectation,
    hp, mul_sub, sum_sub_distrib]

/-- Stage-350 cumulative charging identity, with optional upper bounds on
each true tail. No independence is assumed among the slice events. -/
theorem hardCoreAvailableSlices_le_cumulative (G : SimpleGraph V) (S B : Finset V)
    {z : ℝ} (hz : 0 ≤ z) (cuts c bound : ℕ → ℝ) (n : ℕ)
    (hcuts : ∀ i ≤ n, cuts i ≤ cuts (i+1))
    (hc0 : 0 ≤ c 0) (hcn : 0 ≤ c n)
    (hc : ∀ i < n, c (i+1) ≤ c i)
    (hbound : ∀ i ≤ n, hardCoreAvailableLowerTail G S B z (cuts (i+1)) ≤ bound (i+1)) :
    (∑ i ∈ range (n+1), c i * hardCoreAvailableSlice G S B z (cuts i) (cuts (i+1))) ≤
      c n*bound (n+1) + ∑ i ∈ range n, (c i-c (i+1))*bound (i+1) := by
  have he : (∑ i ∈ range (n+1), c i * hardCoreAvailableSlice G S B z (cuts i) (cuts (i+1))) =
      ∑ i ∈ range (n+1), c i*(hardCoreAvailableLowerTail G S B z (cuts (i+1)) -
        hardCoreAvailableLowerTail G S B z (cuts i)) := by
    apply sum_congr rfl
    intro i hi
    rw [hardCoreAvailableSlice_eq_tail_sub G S B z (hcuts i (Nat.le_of_lt_succ (mem_range.mp hi)))]
  rw [he]
  exact decreasing_prices_le_cumulative c (fun i => hardCoreAvailableLowerTail G S B z (cuts i))
    bound n hc0 hcn hc (hardCoreAvailableLowerTail_nonneg G S B hz (cuts 0)) hbound

#print axioms decreasing_prices_le_cumulative
#print axioms hardCoreAvailableSlice_eq_tail_sub
#print axioms hardCoreAvailableSlices_le_cumulative
end ForestUnimodality
