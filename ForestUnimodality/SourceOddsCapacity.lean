import ForestUnimodality.ForestSourceCapacity
import Mathlib.Algebra.Order.Floor.Semiring

/-! Sharp product-constrained odds capacity with unbounded finite arity.
The saturation proof uses finite induction with a real residual factor and
an integer carry; it does not enumerate graphs or cap the number of children. -/
namespace ForestUnimodality
open Finset

/-- Compress any finite family of factors in [1,1+b] into saturated factors
and one residual factor, without reducing the total available odds bound. -/
theorem finite_odds_saturation {α : Type*} (s : Finset α) (R : α → ℝ)
    {b : ℝ} (hb : 0 < b) (hR : ∀ x ∈ s, 0 ≤ R x ∧ R x ≤ b) :
    ∃ j : ℕ, ∃ r : ℝ, 1 ≤ r ∧ r < 1 + b ∧
      (∏ x ∈ s, (1 + R x)) = (1 + b) ^ j * r ∧
      (∑ x ∈ s, R x) ≤ (j : ℝ) * b + r - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, 1, le_rfl, by linarith, ?_, ?_⟩ <;> simp
  | @insert x s hx ih =>
    have hRx := hR x (mem_insert_self _ _)
    obtain ⟨j, r, hr1, hrB, hprod, hsum⟩ := ih (fun y hy => hR y (mem_insert_of_mem hy))
    have hB : 0 < 1 + b := by linarith
    have hr : 0 < r := by linarith
    have hA : 0 < 1 + R x := by linarith
    by_cases hcarry : (1 + R x) * r < 1 + b
    · refine ⟨j, (1 + R x) * r, ?_, hcarry, ?_, ?_⟩
      · nlinarith [mul_nonneg hRx.1 (sub_nonneg.mpr hr1)]
      · rw [prod_insert hx, hprod]
        ring
      · rw [sum_insert hx]
        nlinarith [mul_nonneg hRx.1 (sub_nonneg.mpr hr1)]
    · have hcarry' : 1 + b ≤ (1 + R x) * r := le_of_not_gt hcarry
      refine ⟨j + 1, (1 + R x) * r / (1 + b), (one_le_div hB).mpr hcarry', ?_, ?_, ?_⟩
      · apply (div_lt_iff₀ hB).mpr
        have ht := mul_lt_mul_of_pos_left hrB hA
        have hl := mul_le_mul_of_nonneg_right (show 1 + R x ≤ 1 + b by linarith) hB.le
        exact ht.trans_le hl
      · rw [prod_insert hx, hprod, pow_succ]
        field_simp
      · rw [sum_insert hx, Nat.cast_add, Nat.cast_one]
        have hpush' : r + R x ≤ b + (1 + R x) * r / (1 + b) := by
          have hpos := mul_nonneg (sub_nonneg.mpr hrB.le) (sub_nonneg.mpr hRx.2)
          have he : (r + R x - b) * (1 + b) ≤ (1 + R x) * r := by nlinarith
          have he' := (le_div_iff₀ hB).mpr he
          linarith
        linarith

noncomputable def sourceOddsCapacity (b T : ℝ) : ℝ :=
  let j := Nat.floor (T / Real.log (1 + b))
  (j : ℝ) * b + Real.exp (T - (j : ℝ) * Real.log (1 + b)) - 1

theorem sourceOddsCapacity_remainder {b T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) :
    0 ≤ T - (Nat.floor (T / Real.log (1 + b)) : ℝ) * Real.log (1 + b) ∧
    T - (Nat.floor (T / Real.log (1 + b)) : ℝ) * Real.log (1 + b) < Real.log (1 + b) := by
  have hL : 0 < Real.log (1 + b) := Real.log_pos (by linarith)
  have hlo := (le_div_iff₀ hL).mp (Nat.floor_le (div_nonneg hT hL.le))
  have hhi := (div_lt_iff₀ hL).mp (Nat.lt_floor_add_one (T / Real.log (1 + b)))
  constructor <;> nlinarith

theorem sourceOddsCapacity_bounds {b T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) :
    (Nat.floor (T / Real.log (1 + b)) : ℝ) * b ≤ sourceOddsCapacity b T ∧
    sourceOddsCapacity b T ≤ ((Nat.floor (T / Real.log (1 + b)) : ℝ) + 1) * b := by
  have hr := sourceOddsCapacity_remainder hb hT
  have hlo : 1 ≤ Real.exp (T - (Nat.floor (T / Real.log (1 + b)) : ℝ) * Real.log (1 + b)) :=
    Real.one_le_exp_iff.mpr hr.1
  have hhi := Real.exp_le_exp.mpr hr.2.le
  rw [Real.exp_log (by linarith : 0 < 1 + b)] at hhi
  unfold sourceOddsCapacity
  constructor <;> linarith


theorem sourceOddsCapacity_mono {b s t : ℝ} (hb : 0 < b) (hs : 0 ≤ s) (hst : s ≤ t) :
    sourceOddsCapacity b s ≤ sourceOddsCapacity b t := by
  have hL : 0 < Real.log (1 + b) := Real.log_pos (by linarith)
  have hj := Nat.floor_mono (div_le_div_of_nonneg_right hst hL.le)
  by_cases he : Nat.floor (s / Real.log (1 + b)) = Nat.floor (t / Real.log (1 + b))
  · unfold sourceOddsCapacity
    rw [he]
    have he := Real.exp_le_exp.mpr (sub_le_sub_right hst
      ((Nat.floor (t / Real.log (1 + b)) : ℝ) * Real.log (1 + b)))
    linarith
  · have hjlt := lt_of_le_of_ne hj he
    have hc : (Nat.floor (s / Real.log (1 + b)) : ℝ) + 1 ≤
        (Nat.floor (t / Real.log (1 + b)) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hjlt
    exact (sourceOddsCapacity_bounds hb hs).2.trans
      ((mul_le_mul_of_nonneg_right hc hb.le).trans (sourceOddsCapacity_bounds hb (hs.trans hst)).1)

/-- Exact saturation with the floor-defined sharp capacity. -/
theorem finite_odds_capacity_exact {α : Type*} (s : Finset α) (R : α → ℝ)
    {b : ℝ} (hb : 0 < b) (hR : ∀ x ∈ s, 0 ≤ R x ∧ R x ≤ b) :
    (∑ x ∈ s, R x) ≤ sourceOddsCapacity b (∑ x ∈ s, Real.log (1 + R x)) := by
  obtain ⟨j, r, hr1, hrB, hprod, hsum⟩ := finite_odds_saturation s R hb hR
  have hB : 0 < 1 + b := by linarith
  have hL : 0 < Real.log (1 + b) := Real.log_pos (by linarith)
  have hr : 0 < r := by linarith
  have hlr0 : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hlrB : Real.log r < Real.log (1 + b) := Real.log_lt_log hr hrB
  have hsumlog : (∑ x ∈ s, Real.log (1 + R x)) = (j : ℝ) * Real.log (1 + b) + Real.log r := by
    rw [← Real.log_prod (fun x hx => ne_of_gt (show 0 < 1 + R x by linarith [(hR x hx).1])),
      hprod, Real.log_mul (pow_ne_zero j hB.ne') hr.ne', Real.log_pow]
  have hS : 0 ≤ ∑ x ∈ s, Real.log (1 + R x) := by
    rw [hsumlog]
    positivity
  have hfloor : Nat.floor ((∑ x ∈ s, Real.log (1 + R x)) / Real.log (1 + b)) = j := by
    apply (Nat.floor_eq_iff (div_nonneg hS hL.le)).mpr
    constructor
    · apply (le_div_iff₀ hL).mpr
      rw [hsumlog]
      linarith
    · apply (div_lt_iff₀ hL).mpr
      rw [hsumlog]
      nlinarith
  have hexp : Real.exp ((∑ x ∈ s, Real.log (1 + R x)) - (j : ℝ) * Real.log (1 + b)) = r := by
    rw [hsumlog]
    ring_nf
    exact Real.exp_log hr
  simpa only [sourceOddsCapacity, hfloor, hexp] using hsum

/-- Sharp odds sum for arbitrary finite size, with a possibly slack log cap. -/
theorem finite_odds_capacity {α : Type*} (s : Finset α) (R : α → ℝ)
    {b T : ℝ} (hb : 0 < b) (hR : ∀ x ∈ s, 0 ≤ R x ∧ R x ≤ b)
    (hT : (∑ x ∈ s, Real.log (1 + R x)) ≤ T) :
    (∑ x ∈ s, R x) ≤ sourceOddsCapacity b T := by
  apply (finite_odds_capacity_exact s R hb hR).trans
  exact sourceOddsCapacity_mono hb (sum_nonneg (fun x hx => Real.log_nonneg (by linarith [(hR x hx).1]))) hT

variable {V : Type*} [DecidableEq V]

theorem SourceMessages.odds_le_activity {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d)
    (hactivity : ∀ x ∈ S, 0 ≤ activity x) {x : V} (hx : x ∈ S) :
    p x / (1 - p x) ≤ activity x := by
  rw [h.odds_eq hx]
  have hc : sourceChildProduct S parent p x ≤ 1 := by
    apply prod_le_one
    · intro y hy
      have hp := h.probability y (mem_filter.mp hy).1
      linarith
    · intro y hy
      have hp := h.probability y (mem_filter.mp hy).1
      linarith
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (hactivity x hx)

/-- The original sharp H_b children-odds bound for genuine extracted messages. -/
theorem SourceMessages.child_odds_capacity {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) {x : V} (hx : x ∈ S) :
    (∑ y ∈ sourceChildren S parent x, p y / (1 - p y)) ≤
      sourceOddsCapacity b (sourceLogCapacity b (p x)) := by
  have hb : 0 < b := (hactivity x hx).1.trans_le (hactivity x hx).2
  apply finite_odds_capacity (sourceChildren S parent x) (fun y => p y / (1 - p y)) hb
  · intro y hy
    have hyS := (mem_filter.mp hy).1
    have hp := h.probability y hyS
    refine ⟨div_nonneg hp.1 (by linarith), ?_⟩
    exact (h.odds_le_activity (fun z hz => (hactivity z hz).1.le) hyS).trans (hactivity y hyS).2
  · have he : (∑ y ∈ sourceChildren S parent x, Real.log (1 + p y / (1 - p y))) =
        ∑ y ∈ sourceChildren S parent x, -Real.log (1 - p y) := by
      apply sum_congr rfl
      intro y hy
      have hn : 1 - p y ≠ 0 := ne_of_gt (sub_pos.mpr (h.probability y (mem_filter.mp hy).1).2)
      have he : 1 + p y / (1 - p y) = (1 - p y)⁻¹ := by field_simp; ring
      rw [he, Real.log_inv]
    rw [he]
    exact h.child_log_sum_le_capacity hactivity hx


omit [DecidableEq V] in
/-- Weighted Cauchy with the exact child-odds weights. -/
theorem source_odds_response_cauchy (s : Finset V) (p d : V → ℝ)
    (hp : ∀ y ∈ s, 0 ≤ p y ∧ p y < 1) :
    (∑ y ∈ s, p y * d y) ^ 2 ≤
      (∑ y ∈ s, p y / (1 - p y)) * (∑ y ∈ s, p y * (1 - p y) * d y ^ 2) := by
  have hden : ∀ y ∈ s, 1 - p y ≠ 0 := fun y hy => ne_of_gt (sub_pos.mpr (hp y hy).2)
  have hc := FiniteTilt.weighted_cauchy s (fun y => p y / (1 - p y))
    (fun _ => 1) (fun y => (1 - p y) * d y)
    (fun y hy => div_nonneg (hp y hy).1 (sub_nonneg.mpr (hp y hy).2.le))
  have hcross : FiniteTilt.numerator s (fun y => p y / (1 - p y))
      (fun y => 1 * ((1 - p y) * d y)) = ∑ y ∈ s, p y * d y := by
    apply sum_congr rfl
    intro y hy
    dsimp only
    have hn := hden y hy
    field_simp
  have hone : FiniteTilt.numerator s (fun y => p y / (1 - p y)) (fun _ => (1 : ℝ) ^ 2) =
      ∑ y ∈ s, p y / (1 - p y) := by simp [FiniteTilt.numerator]
  have hsq : FiniteTilt.numerator s (fun y => p y / (1 - p y))
      (fun y => ((1 - p y) * d y) ^ 2) = ∑ y ∈ s, p y * (1 - p y) * d y ^ 2 := by
    apply sum_congr rfl
    intro y hy
    dsimp only
    have hn := hden y hy
    field_simp
  rwa [hcross, hone, hsq] at hc

/-- Non-divided blocking estimate, including H_b=0 without any convention. -/
theorem SourceMessages.blocking_response_sq_le {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) {x : V} (hx : x ∈ S) :
    (a x - d x) ^ 2 ≤ sourceOddsCapacity b (sourceLogCapacity b (p x)) *
      (∑ y ∈ sourceChildren S parent x, p y * (1 - p y) * d y ^ 2) := by
  have he : a x - d x = ∑ y ∈ sourceChildren S parent x, p y * d y := by
    have hr := h.response x hx
    unfold sourceChildResponse at hr
    linarith
  rw [he]
  apply (source_odds_response_cauchy _ p d (fun y hy => h.probability y (mem_filter.mp hy).1)).trans
  apply mul_le_mul_of_nonneg_right (h.child_odds_capacity hactivity hx)
  apply sum_nonneg
  intro y hy
  have hp := h.probability y (mem_filter.mp hy).1
  exact mul_nonneg (mul_nonneg hp.1 (sub_nonneg.mpr hp.2.le)) (sq_nonneg _)

theorem SourceMessages.blocking_response_capacity {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) {x : V} (hx : x ∈ S) :
    (a x - d x) ^ 2 / sourceOddsCapacity b (sourceLogCapacity b (p x)) ≤
      ∑ y ∈ sourceChildren S parent x, p y * (1 - p y) * d y ^ 2 := by
  have hcap := h.child_odds_capacity hactivity hx
  have hnonneg : 0 ≤ ∑ y ∈ sourceChildren S parent x, p y / (1 - p y) := by
    apply sum_nonneg
    intro y hy
    have hp := h.probability y (mem_filter.mp hy).1
    exact div_nonneg hp.1 (sub_nonneg.mpr hp.2.le)
  have hH : 0 ≤ sourceOddsCapacity b (sourceLogCapacity b (p x)) := hnonneg.trans hcap
  by_cases hz : sourceOddsCapacity b (sourceLogCapacity b (p x)) = 0
  · rw [hz, div_zero]
    apply sum_nonneg
    intro y hy
    have hp := h.probability y (mem_filter.mp hy).1
    exact mul_nonneg (mul_nonneg hp.1 (sub_nonneg.mpr hp.2.le)) (sq_nonneg _)
  · apply (div_le_iff₀ (lt_of_le_of_ne hH (Ne.symm hz))).mpr
    have hb := h.blocking_response_sq_le hactivity hx
    nlinarith [hb]

/-- Exact parent-marginal transfer, with root mass zero. -/
theorem SourceMessages.sum_parent_marginal {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) (cost : V → ℝ) :
    (∑ x ∈ S, heterogeneousMarginal G S activity x * ∑ y ∈ sourceChildren S parent x, cost y) =
      ∑ y ∈ S, sourceParentMass G S activity (parent y) * cost y := by
  classical
  simp only [sourceChildren, sum_filter, mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro y hy
  cases hp : parent y with
  | none => simp [sourceParentMass]
  | some x =>
    have hx := (h.parent_mem y hy x hp).1
    simp [sourceParentMass, hx]

/-- Complete genuine blocking budget in an equivalent marginal form. -/
theorem SourceMessages.blocking_capacity_budget {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) :
    (∑ x ∈ S, (heterogeneousMarginal G S activity x *
      ((a x - d x) ^ 2 / sourceOddsCapacity b (sourceLogCapacity b (p x))) -
      (p x - heterogeneousMarginal G S activity x) * (1 - p x) * d x ^ 2)) ≤ 0 := by
  have hlocal := sum_le_sum (s := S) (fun x hx =>
    mul_le_mul_of_nonneg_left (h.blocking_response_capacity hactivity hx)
      (heterogeneousMarginal_mem_Icc G S activity (fun y hy => (hactivity y hy).1.le) x).1)
  have htransfer := h.sum_parent_marginal (fun y => p y * (1 - p y) * d y ^ 2)
  have he : (∑ y ∈ S, sourceParentMass G S activity (parent y) * (p y * (1 - p y) * d y ^ 2)) =
      ∑ y ∈ S, (p y - heterogeneousMarginal G S activity y) * (1 - p y) * d y ^ 2 := by
    apply sum_congr rfl
    intro y hy
    have hm := h.marginal y hy
    have hm' : sourceParentMass G S activity (parent y) * p y = p y - heterogeneousMarginal G S activity y := by
      nlinarith [hm]
    calc
      _ = (sourceParentMass G S activity (parent y) * p y) * (1 - p y) * d y ^ 2 := by ring
      _ = _ := by rw [hm']
  rw [he] at htransfer
  rw [sum_sub_distrib]
  linarith

/-- The exact original r=pi/p blocking row, including all signed responses. -/
noncomputable def sourceBlockingBudget (G : SimpleGraph V) (S : Finset V)
    (activity a p d : V → ℝ) (b : ℝ) : ℝ :=
  ∑ x ∈ S, p x * ((heterogeneousMarginal G S activity x / p x) *
    ((a x - d x) ^ 2 / sourceOddsCapacity b (sourceLogCapacity b (p x))) -
    (1 - heterogeneousMarginal G S activity x / p x) * (1 - p x) * d x ^ 2)

theorem SourceMessages.blocking_capacity_budget_scaled {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) :
    sourceBlockingBudget G S activity a p d b ≤ 0 := by
  convert h.blocking_capacity_budget hactivity using 1
  unfold sourceBlockingBudget
  apply sum_congr rfl
  intro x hx
  have hp : p x ≠ 0 := (h.probability_pos (fun y hy => (hactivity y hy).1) hx).ne'
  by_cases hH : sourceOddsCapacity b (sourceLogCapacity b (p x)) = 0
  · simp only [hH, div_zero, mul_zero, zero_sub]
    field_simp
  · field_simp

/-- Actual forests supply the same messages for sharp blocking, real mean,
and real variance. No message system is an external forest hypothesis. -/
theorem exists_forest_source_blocking (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (activity a : V → ℝ) (b : ℝ)
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) :
    ∃ parent p d, SourceMessages G S activity a parent p d ∧
      heterogeneousMean G S activity (markedSum a) = ∑ x ∈ S, p x * d x ∧
      heterogeneousVariance G S activity (markedSum a) =
        (∑ x ∈ S, heterogeneousMarginal G S activity x * (1 - p x) * d x ^ 2) ∧
      sourceBlockingBudget G S activity a p d b ≤ 0 := by
  obtain ⟨parent, p, d, hm, hmean, hvar⟩ := exists_forest_source_messages_moments G hG S activity a
    (fun x hx => (hactivity x hx).1.le)
  exact ⟨parent, p, d, hm, hmean, hvar, hm.blocking_capacity_budget_scaled hactivity⟩

#print axioms finite_odds_saturation
#print axioms finite_odds_capacity
#print axioms SourceMessages.child_odds_capacity
#print axioms SourceMessages.blocking_response_sq_le
#print axioms SourceMessages.blocking_capacity_budget_scaled
#print axioms exists_forest_source_blocking
end ForestUnimodality

