import ForestUnimodality.ForestSourceMessages
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Genuine forest source capacity estimates for arbitrarily many children.
No graph size or child count is bounded. Numerical source constants are not
assumed; the estimates follow from the actual extracted message equations. -/

namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

noncomputable def sourceLogCapacity (b p : ℝ) : ℝ := Real.log (b * (1 - p) / p)

/-- The first atanh-series term gives the stronger capacity weight p/(1-p/2). -/
theorem source_probability_log_bound {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    p / (1 - p / 2) ≤ -Real.log (1 - p) := by
  have hd : 0 < 2 - p := by linarith
  have hq0 : 0 ≤ p / (2 - p) := div_nonneg hp0 hd.le
  have hq1 : p / (2 - p) < 1 := (div_lt_one hd).mpr (by linarith)
  have h := Real.sum_range_le_log_div hq0 hq1 1
  norm_num at h
  have he : (1 + p / (2 - p)) / (1 - p / (2 - p)) = (1 - p)⁻¹ := by
    have h1 : 1 - p ≠ 0 := ne_of_gt (by linarith)
    apply (div_eq_iff (ne_of_gt (sub_pos.mpr hq1))).mpr
    field_simp
    ring
  rw [he, Real.log_inv] at h
  have hf : p / (1 - p / 2) = 2 * (p / (2 - p)) := by
    field_simp
  rw [hf]
  linarith

theorem SourceMessages.child_log_sum_le_capacity {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) {x : V} (hx : x ∈ S) :
    (∑ y ∈ sourceChildren S parent x, -Real.log (1 - p y)) ≤ sourceLogCapacity b (p x) := by
  have hp := h.probability_pos (fun y hy => (hactivity y hy).1) hx
  have h1 : 0 < 1 - p x := sub_pos.mpr (h.probability x hx).2
  have hb : 0 < b := (hactivity x hx).1.trans_le (hactivity x hx).2
  have he := h.log_odds (fun y hy => (hactivity y hy).1) hx
  have hl := Real.log_le_log (hactivity x hx).1 (hactivity x hx).2
  unfold sourceLogCapacity
  rw [Real.log_div (mul_ne_zero hb.ne' h1.ne') hp.ne', Real.log_mul hb.ne' h1.ne']
  simp only [sum_neg_distrib]
  linarith

/-- The true logarithmic capacity bound; valid for every finite child set. -/
theorem SourceMessages.child_capacity {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) {x : V} (hx : x ∈ S) :
    (∑ y ∈ sourceChildren S parent x, p y / (1 - p y / 2)) ≤ sourceLogCapacity b (p x) := by
  apply le_trans ?_ (h.child_log_sum_le_capacity hactivity hx)
  exact sum_le_sum (fun y hy => source_probability_log_bound
    (h.probability y (mem_filter.mp hy).1).1 (h.probability y (mem_filter.mp hy).1).2)

omit [DecidableEq V] in
/-- Finite weighted Cauchy in the exact response-capacity weights. -/
theorem source_weighted_response_cauchy (s : Finset V) (p d : V → ℝ)
    (hp : ∀ y ∈ s, 0 ≤ p y ∧ p y < 1) :
    (∑ y ∈ s, p y * d y) ^ 2 ≤
      (∑ y ∈ s, p y / (1 - p y / 2)) * (∑ y ∈ s, p y * (1 - p y / 2) * d y ^ 2) := by
  have hden : ∀ y ∈ s, 1 - p y / 2 ≠ 0 := fun y hy => ne_of_gt (by linarith [(hp y hy).2])
  have hc := FiniteTilt.weighted_cauchy s (fun y => p y / (1 - p y / 2))
    (fun _ => 1) (fun y => (1 - p y / 2) * d y)
    (fun y hy => div_nonneg (hp y hy).1 (by linarith [(hp y hy).2]))
  have hcross : FiniteTilt.numerator s (fun y => p y / (1 - p y / 2))
      (fun y => 1 * ((1 - p y / 2) * d y)) = ∑ y ∈ s, p y * d y := by
    apply sum_congr rfl
    intro y hy
    dsimp only
    have hn : 2 - p y ≠ 0 := ne_of_gt (by linarith [(hp y hy).2])
    field_simp
  have hone : FiniteTilt.numerator s (fun y => p y / (1 - p y / 2)) (fun _ => (1 : ℝ) ^ 2) =
      ∑ y ∈ s, p y / (1 - p y / 2) := by simp [FiniteTilt.numerator]
  have hsq : FiniteTilt.numerator s (fun y => p y / (1 - p y / 2))
      (fun y => ((1 - p y / 2) * d y) ^ 2) = ∑ y ∈ s, p y * (1 - p y / 2) * d y ^ 2 := by
    apply sum_congr rfl
    intro y hy
    dsimp only
    field_simp
  rwa [hcross, hone, hsq] at hc

omit [DecidableEq V] in
/-- A positive-part response bound, including zero capacity. The finite set
has no cardinality restriction. -/
theorem source_positive_response_capacity (s : Finset V) (p d : V → ℝ) (T : ℝ)
    (hp : ∀ y ∈ s, 0 ≤ p y ∧ p y < 1)
    (hcapacity : (∑ y ∈ s, p y / (1 - p y / 2)) ≤ T) :
    (max 0 (∑ y ∈ s, p y * d y)) ^ 2 / T ≤
      ∑ y ∈ s, p y * (1 - p y / 2) * (max 0 (d y)) ^ 2 := by
  have hden : ∀ y ∈ s, 0 ≤ 1 - p y / 2 := fun y hy => by linarith [(hp y hy).2]
  have hE : 0 ≤ ∑ y ∈ s, p y * (1 - p y / 2) * (max 0 (d y)) ^ 2 :=
    sum_nonneg (fun y hy => mul_nonneg (mul_nonneg (hp y hy).1 (hden y hy)) (sq_nonneg _))
  have hT : 0 ≤ T := (sum_nonneg (fun y hy => div_nonneg (hp y hy).1 (hden y hy))).trans hcapacity
  by_cases hT0 : T = 0
  · rw [hT0, div_zero]
    exact hE
  have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
  apply (div_le_iff₀ hTpos).mpr
  have hsnonneg : 0 ≤ ∑ y ∈ s, p y * max 0 (d y) :=
    sum_nonneg (fun y hy => mul_nonneg (hp y hy).1 (le_max_left _ _))
  have hmax : max 0 (∑ y ∈ s, p y * d y) ≤ ∑ y ∈ s, p y * max 0 (d y) := by
    apply max_le hsnonneg
    exact sum_le_sum (fun y hy => mul_le_mul_of_nonneg_left (le_max_right _ _) (hp y hy).1)
  have hsquare := pow_le_pow_left₀ (le_max_left 0 (∑ y ∈ s, p y * d y)) hmax 2
  have hc := source_weighted_response_cauchy s p (fun y => max 0 (d y)) hp
  have he := mul_le_mul_of_nonneg_right hcapacity hE
  nlinarith

theorem SourceMessages.positive_response_capacity {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) {x : V} (hx : x ∈ S) :
    (max 0 (a x - d x)) ^ 2 / sourceLogCapacity b (p x) ≤
      ∑ y ∈ sourceChildren S parent x, p y * (1 - p y / 2) * (max 0 (d y)) ^ 2 := by
  have he : a x - d x = ∑ y ∈ sourceChildren S parent x, p y * d y := by
    have hr := h.response x hx
    unfold sourceChildResponse at hr
    linarith
  rw [he]
  exact source_positive_response_capacity _ p d _
    (fun y hy => h.probability y (mem_filter.mp hy).1) (h.child_capacity hactivity hx)

theorem SourceMessages.negative_response_capacity {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) {x : V} (hx : x ∈ S) :
    (max 0 (d x - a x)) ^ 2 / sourceLogCapacity b (p x) ≤
      ∑ y ∈ sourceChildren S parent x, p y * (1 - p y / 2) * (max 0 (-d y)) ^ 2 := by
  have he : d x - a x = ∑ y ∈ sourceChildren S parent x, p y * (-d y) := by
    have hr := h.response x hx
    unfold sourceChildResponse at hr
    simp only [mul_neg, sum_neg_distrib]
    linarith
  rw [he]
  exact source_positive_response_capacity _ p (fun y => -d y) _
    (fun y hy => h.probability y (mem_filter.mp hy).1) (h.child_capacity hactivity hx)


noncomputable def sourceParentMark (a : V → ℝ) (o : Option V) : ℝ :=
  match o with
  | none => 0
  | some y => a y

/-- Unique-parent counting transports arbitrary nonnegative source prices.
Roots contribute only the additional nonnegative right-hand term. -/
theorem SourceMessages.sum_parent_price_le {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) (price : ℝ → ℝ) (cost : V → ℝ)
    (hroot : 0 ≤ price 0) (hcost : ∀ y ∈ S, 0 ≤ cost y) :
    (∑ x ∈ S, price (a x) * ∑ y ∈ sourceChildren S parent x, cost y) ≤
      ∑ y ∈ S, price (sourceParentMark a (parent y)) * cost y := by
  classical
  simp only [sourceChildren, sum_filter, mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  apply sum_le_sum
  intro y hy
  cases hp : parent y with
  | none => simpa [sourceParentMark] using mul_nonneg hroot (hcost y hy)
  | some x =>
    have hx := (h.parent_mem y hy x hp).1
    simp [sourceParentMark, hx]

/-- Global positive-response budget with an arbitrary nonnegative price
function on the real source marks. Indicator sources are a special case. -/
theorem SourceMessages.positive_capacity_budget {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b)
    (price : ℝ → ℝ) (hprice : ∀ t, 0 ≤ price t) :
    (∑ x ∈ S, (price (a x) * ((max 0 (a x - d x)) ^ 2 / sourceLogCapacity b (p x)) -
      price (sourceParentMark a (parent x)) * p x * (1 - p x / 2) * (max 0 (d x)) ^ 2)) ≤ 0 := by
  have hcost : ∀ x ∈ S, 0 ≤ p x * (1 - p x / 2) * (max 0 (d x)) ^ 2 := by
    intro x hx
    have hp := h.probability x hx
    exact mul_nonneg (mul_nonneg hp.1 (by linarith)) (sq_nonneg _)
  have hlocal := sum_le_sum (s := S) (fun x hx =>
    mul_le_mul_of_nonneg_left (h.positive_response_capacity hactivity hx) (hprice (a x)))
  have hglobal := h.sum_parent_price_le price
    (fun x => p x * (1 - p x / 2) * (max 0 (d x)) ^ 2) (hprice 0) hcost
  have he : (∑ x ∈ S, price (sourceParentMark a (parent x)) *
      (p x * (1 - p x / 2) * (max 0 (d x)) ^ 2)) =
      ∑ x ∈ S, price (sourceParentMark a (parent x)) * p x * (1 - p x / 2) * (max 0 (d x)) ^ 2 := by
    apply sum_congr rfl
    intro x _
    ring
  rw [he] at hglobal
  rw [sum_sub_distrib]
  linarith

theorem SourceMessages.negative_capacity_budget {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b)
    (price : ℝ → ℝ) (hprice : ∀ t, 0 ≤ price t) :
    (∑ x ∈ S, (price (a x) * ((max 0 (d x - a x)) ^ 2 / sourceLogCapacity b (p x)) -
      price (sourceParentMark a (parent x)) * p x * (1 - p x / 2) * (max 0 (-d x)) ^ 2)) ≤ 0 := by
  have hcost : ∀ x ∈ S, 0 ≤ p x * (1 - p x / 2) * (max 0 (-d x)) ^ 2 := by
    intro x hx
    have hp := h.probability x hx
    exact mul_nonneg (mul_nonneg hp.1 (by linarith)) (sq_nonneg _)
  have hlocal := sum_le_sum (s := S) (fun x hx =>
    mul_le_mul_of_nonneg_left (h.negative_response_capacity hactivity hx) (hprice (a x)))
  have hglobal := h.sum_parent_price_le price
    (fun x => p x * (1 - p x / 2) * (max 0 (-d x)) ^ 2) (hprice 0) hcost
  have he : (∑ x ∈ S, price (sourceParentMark a (parent x)) *
      (p x * (1 - p x / 2) * (max 0 (-d x)) ^ 2)) =
      ∑ x ∈ S, price (sourceParentMark a (parent x)) * p x * (1 - p x / 2) * (max 0 (-d x)) ^ 2 := by
    apply sum_congr rfl
    intro x _
    ring
  rw [he] at hglobal
  rw [sum_sub_distrib]
  linarith

/-- The exact Lambda-scaled positive row from the source proof. At T=0,
Lean's division convention is harmless: the local source difference vanishes,
and the preceding non-divided capacity inequality includes this boundary. -/
noncomputable def sourcePositiveCapacityBudget (S : Finset V) (a : V → ℝ)
    (parent : V → Option V) (p d : V → ℝ) (b : ℝ) (price : ℝ → ℝ) : ℝ :=
  ∑ x ∈ S, p x * (price (a x) * (1 / (p x * sourceLogCapacity b (p x))) *
    (max 0 (a x - d x)) ^ 2 - price (sourceParentMark a (parent x)) *
      (1 - p x / 2) * (max 0 (d x)) ^ 2)

noncomputable def sourceNegativeCapacityBudget (S : Finset V) (a : V → ℝ)
    (parent : V → Option V) (p d : V → ℝ) (b : ℝ) (price : ℝ → ℝ) : ℝ :=
  ∑ x ∈ S, p x * (price (a x) * (1 / (p x * sourceLogCapacity b (p x))) *
    (max 0 (d x - a x)) ^ 2 - price (sourceParentMark a (parent x)) *
      (1 - p x / 2) * (max 0 (-d x)) ^ 2)

theorem SourceMessages.positive_capacity_budget_scaled {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b)
    (price : ℝ → ℝ) (hprice : ∀ t, 0 ≤ price t) :
    sourcePositiveCapacityBudget S a parent p d b price ≤ 0 := by
  convert h.positive_capacity_budget hactivity price hprice using 1
  unfold sourcePositiveCapacityBudget
  apply sum_congr rfl
  intro x hx
  have hp : p x ≠ 0 := (h.probability_pos (fun y hy => (hactivity y hy).1) hx).ne'
  by_cases hT : sourceLogCapacity b (p x) = 0
  · simp only [hT, mul_zero, div_zero, mul_zero, zero_sub]
    ring
  · field_simp

theorem SourceMessages.negative_capacity_budget_scaled {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b)
    (price : ℝ → ℝ) (hprice : ∀ t, 0 ≤ price t) :
    sourceNegativeCapacityBudget S a parent p d b price ≤ 0 := by
  convert h.negative_capacity_budget hactivity price hprice using 1
  unfold sourceNegativeCapacityBudget
  apply sum_congr rfl
  intro x hx
  have hp : p x ≠ 0 := (h.probability_pos (fun y hy => (hactivity y hy).1) hx).ne'
  by_cases hT : sourceLogCapacity b (p x) = 0
  · simp only [hT, mul_zero, div_zero, mul_zero, zero_sub]
    ring
  · field_simp

/-- Actual-forest version: the messages and both budgets are constructed from
the real hard-core distribution, with its real source mean and variance. -/
theorem exists_forest_source_capacity (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (activity a : V → ℝ) (b : ℝ)
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) :
    ∃ parent p d, SourceMessages G S activity a parent p d ∧
      heterogeneousMean G S activity (markedSum a) = ∑ x ∈ S, p x * d x ∧
      heterogeneousVariance G S activity (markedSum a) =
        (∑ x ∈ S, heterogeneousMarginal G S activity x * (1 - p x) * d x ^ 2) ∧
      ∀ price : ℝ → ℝ, (∀ t, 0 ≤ price t) →
        sourcePositiveCapacityBudget S a parent p d b price ≤ 0 ∧
        sourceNegativeCapacityBudget S a parent p d b price ≤ 0 := by
  obtain ⟨parent, p, d, hm, hmean, hvar⟩ := exists_forest_source_messages_moments G hG S activity a
    (fun x hx => (hactivity x hx).1.le)
  exact ⟨parent, p, d, hm, hmean, hvar, fun price hprice =>
    ⟨hm.positive_capacity_budget_scaled hactivity price hprice,
      hm.negative_capacity_budget_scaled hactivity price hprice⟩⟩

/-- A zero true capacity forces the response to equal the local source mark.
This justifies the zero-capacity convention independently of real division. -/
theorem SourceMessages.eq_mark_of_capacity_zero {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) {x : V} (hx : x ∈ S)
    (hzero : sourceLogCapacity b (p x) = 0) : d x = a x := by
  have hp := fun y (hy : y ∈ sourceChildren S parent x) => h.probability y (mem_filter.mp hy).1
  have hc := h.child_capacity hactivity hx
  rw [hzero] at hc
  have hnonneg : 0 ≤ ∑ y ∈ sourceChildren S parent x, p y / (1 - p y / 2) := by
    apply sum_nonneg
    intro y hy
    exact div_nonneg (hp y hy).1 (by linarith [(hp y hy).2])
  have hsum := le_antisymm hc hnonneg
  have hsq := source_weighted_response_cauchy (sourceChildren S parent x) p d hp
  rw [hsum, zero_mul] at hsq
  have hr := h.response x hx
  unfold sourceChildResponse at hr
  nlinarith [sq_nonneg (∑ y ∈ sourceChildren S parent x, p y * d y)]
#print axioms source_probability_log_bound
#print axioms SourceMessages.child_capacity
#print axioms SourceMessages.positive_response_capacity
#print axioms SourceMessages.negative_response_capacity
#print axioms SourceMessages.positive_capacity_budget_scaled
#print axioms SourceMessages.negative_capacity_budget_scaled
#print axioms SourceMessages.eq_mark_of_capacity_zero
#print axioms exists_forest_source_capacity
end ForestUnimodality



