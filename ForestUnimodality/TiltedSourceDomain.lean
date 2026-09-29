import ForestUnimodality.SourceMixtureCertificate

/-! Message-domain facts with the activity cap of the current vertex or its
actual parent. These permit a genuinely heterogeneous fixed-B source. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

theorem SourceMessages.probability_le_local_bound {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    {x : V} (hactivity : ∀ y ∈ S, 0 < activity y) (hbound : activity x ≤ b) (hx : x ∈ S) :
    p x ≤ b / (1 + b) := by
  have hb : 0 < b := (hactivity x hx).trans_le hbound
  have ho := (h.odds_le_activity (fun y hy => (hactivity y hy).le) hx).trans hbound
  have hp1 := sub_pos.mpr (h.probability x hx).2
  have ho' := (div_le_iff₀ hp1).mp ho
  apply (le_div_iff₀ (by linarith : 0 < 1 + b)).mpr
  nlinarith

theorem SourceMessages.child_log_sum_le_local_capacity {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    {x : V} (hactivity : ∀ y ∈ S, 0 < activity y) (hbound : activity x ≤ b) (hx : x ∈ S) :
    (∑ y ∈ sourceChildren S parent x, -Real.log (1 - p y)) ≤ sourceLogCapacity b (p x) := by
  have hp := h.probability_pos (fun y hy => (hactivity y hy)) hx
  have h1 : 0 < 1 - p x := sub_pos.mpr (h.probability x hx).2
  have hb : 0 < b := (hactivity x hx).trans_le hbound
  have he := h.log_odds (fun y hy => (hactivity y hy)) hx
  have hl := Real.log_le_log (hactivity x hx) hbound
  unfold sourceLogCapacity
  rw [Real.log_div (mul_ne_zero hb.ne' h1.ne') hp.ne', Real.log_mul hb.ne' h1.ne']
  simp only [sum_neg_distrib]
  linarith

theorem SourceMessages.child_local_capacity {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    {x : V} (hactivity : ∀ y ∈ S, 0 < activity y) (hbound : activity x ≤ b) (hx : x ∈ S) :
    (∑ y ∈ sourceChildren S parent x, p y / (1 - p y / 2)) ≤ sourceLogCapacity b (p x) := by
  apply le_trans ?_ (h.child_log_sum_le_local_capacity hactivity hbound hx)
  exact sum_le_sum (fun y hy => source_probability_log_bound
    (h.probability y (mem_filter.mp hy).1).1 (h.probability y (mem_filter.mp hy).1).2)

theorem SourceMessages.positive_response_local_capacity {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    {x : V} (hactivity : ∀ y ∈ S, 0 < activity y) (hbound : activity x ≤ b) (hx : x ∈ S) :
    (max 0 (a x - d x)) ^ 2 / sourceLogCapacity b (p x) ≤
      ∑ y ∈ sourceChildren S parent x, p y * (1 - p y / 2) * (max 0 (d y)) ^ 2 := by
  have he : a x - d x = ∑ y ∈ sourceChildren S parent x, p y * d y := by
    have hr := h.response x hx
    unfold sourceChildResponse at hr
    linarith
  rw [he]
  exact source_positive_response_capacity _ p d _
    (fun y hy => h.probability y (mem_filter.mp hy).1) (h.child_local_capacity hactivity hbound hx)

theorem SourceMessages.negative_response_local_capacity {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    {x : V} (hactivity : ∀ y ∈ S, 0 < activity y) (hbound : activity x ≤ b) (hx : x ∈ S) :
    (max 0 (d x - a x)) ^ 2 / sourceLogCapacity b (p x) ≤
      ∑ y ∈ sourceChildren S parent x, p y * (1 - p y / 2) * (max 0 (-d y)) ^ 2 := by
  have he : d x - a x = ∑ y ∈ sourceChildren S parent x, p y * (-d y) := by
    have hr := h.response x hx
    unfold sourceChildResponse at hr
    simp only [mul_neg, sum_neg_distrib]
    linarith
  rw [he]
  exact source_positive_response_capacity _ p (fun y => -d y) _
    (fun y hy => h.probability y (mem_filter.mp hy).1) (h.child_local_capacity hactivity hbound hx)

theorem SourceMessages.retention_bounds_local_parent {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hb : 0<b) (hactivity : ∀ y ∈ S, 0 < activity y) {x : V} (hx : x ∈ S)
    (hbound : ∀y, parent x=some y → activity y≤b) :
    1 / (1 + b * (1 - p x)) ≤ heterogeneousMarginal G S activity x / p x ∧
      heterogeneousMarginal G S activity x / p x ≤ 1 := by
  have hp := h.probability_pos (fun y hy => (hactivity y hy)) hx
  have hp1 := sub_pos.mpr (h.probability x hx).2
  have hB : 0 < 1 + b * (1 - p x) := by positivity
  have hnonneg : ∀ y ∈ S, 0 ≤ activity y := fun y hy => (hactivity y hy).le
  have hratio : heterogeneousMarginal G S activity x / p x =
      1 - sourceParentMass G S activity (parent x) := by
    rw [h.marginal x hx]
    exact mul_div_cancel_left₀ _ hp.ne'
  refine ⟨?_, (div_le_one hp).mpr (h.marginal_le_probability hnonneg hx)⟩
  have hparent : sourceParentMass G S activity (parent x) ≤
      b * (1 - p x) / (1 + b * (1 - p x)) := by
    cases he : parent x with
    | none => exact div_nonneg (mul_nonneg hb.le hp1.le) hB.le
    | some y =>
      have hy := (h.parent_mem x hx y he).1
      have hxy : x ∈ sourceChildren S parent y := mem_filter.mpr ⟨hx, he⟩
      have hprod := h.child_product_le_factor hxy
      have hodds : p y / (1 - p y) ≤ b * (1 - p x) := by
        rw [h.odds_eq hy]
        exact (mul_le_mul_of_nonneg_left hprod (hactivity y hy).le).trans
          (mul_le_mul_of_nonneg_right (hbound y he) hp1.le)
      have hpy1 := sub_pos.mpr (h.probability y hy).2
      have hodds' := (div_le_iff₀ hpy1).mp hodds
      have hpy : p y ≤ b * (1 - p x) / (1 + b * (1 - p x)) := by
        apply (le_div_iff₀ hB).mpr
        nlinarith
      exact (h.marginal_le_probability hnonneg hy).trans hpy
  have he : 1 / (1 + b * (1 - p x)) = 1 - b * (1 - p x) / (1 + b * (1 - p x)) := by field_simp; ring
  rw [hratio, he]
  linarith

theorem SourceMessages.response_at_local_probability_endpoint {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ} {x : V}
    (hactivity : ∀ y∈S, 0<activity y) (hbound : activity x≤b) (hx : x∈S)
    (he : p x=b/(1+b)) : d x=a x := by
  have hb : 0<b := (hactivity x hx).trans_le hbound
  have hcap := h.child_local_capacity hactivity hbound hx
  have hzero : sourceLogCapacity b (p x)=0 := by
    unfold sourceLogCapacity
    rw [he]
    have hB : 0<1+b := by linarith
    have hh : b*(1-b/(1+b))/(b/(1+b))=1 := by field_simp; ring
    rw [hh,Real.log_one]
  rw [hzero] at hcap
  have hemp : sourceChildren S parent x=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hpy := h.probability_pos hactivity (mem_filter.mp hy).1
    have hpy1 := (h.probability y (mem_filter.mp hy).1).2
    have hterm : 0<p y/(1-p y/2) := div_pos hpy (by linarith)
    have hs := single_le_sum (s:=sourceChildren S parent x)
      (f:=fun z=>p z/(1-p z/2)) (fun z hz=>div_nonneg
        (h.probability z (mem_filter.mp hz).1).1 (by linarith [(h.probability z (mem_filter.mp hz).1).2])) hy
    linarith
  have hr := h.response x hx
  simpa only [sourceChildResponse,hemp,sum_empty,sub_zero] using hr

theorem SourceMessages.positive_variable_capacity_budget {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) (cap : V→ℝ)
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ cap x)
    (price : ℝ → ℝ) (hprice : ∀ t, 0 ≤ price t) :
    (∑ x ∈ S, (price (a x) * ((max 0 (a x - d x)) ^ 2 / sourceLogCapacity (cap x) (p x)) -
      price (sourceParentMark a (parent x)) * p x * (1 - p x / 2) * (max 0 (d x)) ^ 2)) ≤ 0 := by
  have hcost : ∀ x ∈ S, 0 ≤ p x * (1 - p x / 2) * (max 0 (d x)) ^ 2 := by
    intro x hx
    have hp := h.probability x hx
    exact mul_nonneg (mul_nonneg hp.1 (by linarith)) (sq_nonneg _)
  have hlocal := sum_le_sum (s := S) (fun x hx =>
    mul_le_mul_of_nonneg_left (h.positive_response_local_capacity (fun y hy=>(hactivity y hy).1) (hactivity x hx).2 hx) (hprice (a x)))
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


theorem SourceMessages.negative_variable_capacity_budget {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) (cap : V→ℝ)
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ cap x)
    (price : ℝ → ℝ) (hprice : ∀ t, 0 ≤ price t) :
    (∑ x ∈ S, (price (a x) * ((max 0 (d x - a x)) ^ 2 / sourceLogCapacity (cap x) (p x)) -
      price (sourceParentMark a (parent x)) * p x * (1 - p x / 2) * (max 0 (-d x)) ^ 2)) ≤ 0 := by
  have hcost : ∀ x ∈ S, 0 ≤ p x * (1 - p x / 2) * (max 0 (-d x)) ^ 2 := by
    intro x hx
    have hp := h.probability x hx
    exact mul_nonneg (mul_nonneg hp.1 (by linarith)) (sq_nonneg _)
  have hlocal := sum_le_sum (s := S) (fun x hx =>
    mul_le_mul_of_nonneg_left (h.negative_response_local_capacity (fun y hy=>(hactivity y hy).1) (hactivity x hx).2 hx) (hprice (a x)))
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


#print axioms SourceMessages.probability_le_local_bound
#print axioms SourceMessages.retention_bounds_local_parent
#print axioms SourceMessages.response_at_local_probability_endpoint
#print axioms SourceMessages.positive_variable_capacity_budget
#print axioms SourceMessages.negative_variable_capacity_budget
end ForestUnimodality
