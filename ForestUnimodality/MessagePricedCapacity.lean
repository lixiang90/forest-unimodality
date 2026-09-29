import ForestUnimodality.ExactLogCapacity

/-! Message-dependent source prices are transported along the actual parent
map. All vertices, including roots, participate in the same finite sum. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

theorem SourceMessages.exact_positive_capacity_budget
    {G : SimpleGraph V} {S : Finset V} {activity a : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b)
    (weight : V → ℝ) (hw : ∀ x ∈ S, 0 ≤ weight x) :
    (∑ x ∈ S, (weight x * ((max 0 (a x - d x)) ^ 2 / sourceLogCapacity b (p x)) -
      sourceParentMark weight (parent x) * (p x * sourceExactH (p x) * (max 0 (d x)) ^ 2))) ≤ 0 := by
  rw [sum_sub_distrib]
  apply sub_nonpos.mpr
  calc
    _ ≤ ∑ x ∈ S, weight x * ∑ y ∈ sourceChildren S parent x,
        p y * sourceExactH (p y) * (max 0 (d y)) ^ 2 :=
      sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left
        (h.exact_positive_response_capacity hactivity hx) (hw x hx))
    _ = _ := h.sum_parent_mark_eq weight _

theorem SourceMessages.exact_negative_capacity_budget
    {G : SimpleGraph V} {S : Finset V} {activity a : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b)
    (weight : V → ℝ) (hw : ∀ x ∈ S, 0 ≤ weight x) :
    (∑ x ∈ S, (weight x * ((max 0 (d x - a x)) ^ 2 / sourceLogCapacity b (p x)) -
      sourceParentMark weight (parent x) * (p x * sourceExactH (p x) * (max 0 (-d x)) ^ 2))) ≤ 0 := by
  rw [sum_sub_distrib]
  apply sub_nonpos.mpr
  calc
    _ ≤ ∑ x ∈ S, weight x * ∑ y ∈ sourceChildren S parent x,
        p y * sourceExactH (p y) * (max 0 (-d y)) ^ 2 :=
      sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left
        (h.exact_negative_response_capacity hactivity hx) (hw x hx))
    _ = _ := h.sum_parent_mark_eq weight _

private theorem scale_capacity {p T w A parentWeight H D : ℝ} (hp : p ≠ 0) :
    p * (w * (1 / (p * T)) * A - parentWeight * H * D) =
      w * (A / T) - parentWeight * (p * H * D) := by
  by_cases hT : T = 0
  · simp only [hT, mul_zero, div_zero, zero_mul, zero_sub]
    ring
  · field_simp

theorem SourceMessages.exact_positive_capacity_budget_scaled
    {G : SimpleGraph V} {S : Finset V} {activity a : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b)
    (weight : V → ℝ) (hw : ∀ x ∈ S, 0 ≤ weight x) :
    (∑ x ∈ S, p x *
      (weight x * (1 / (p x * sourceLogCapacity b (p x))) * (max 0 (a x - d x)) ^ 2 -
        sourceParentMark weight (parent x) * sourceExactH (p x) * (max 0 (d x)) ^ 2)) ≤ 0 := by
  have he : (∑ x ∈ S, p x *
      (weight x * (1 / (p x * sourceLogCapacity b (p x))) * (max 0 (a x - d x)) ^ 2 -
        sourceParentMark weight (parent x) * sourceExactH (p x) * (max 0 (d x)) ^ 2)) =
      ∑ x ∈ S, (weight x * ((max 0 (a x - d x)) ^ 2 / sourceLogCapacity b (p x)) -
        sourceParentMark weight (parent x) * (p x * sourceExactH (p x) * (max 0 (d x)) ^ 2)) := by
    apply sum_congr rfl
    intro x hx
    exact scale_capacity (h.probability_pos (fun y hy => (hactivity y hy).1) hx).ne'
  rw [he]
  exact h.exact_positive_capacity_budget hactivity weight hw

theorem SourceMessages.exact_negative_capacity_budget_scaled
    {G : SimpleGraph V} {S : Finset V} {activity a : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b)
    (weight : V → ℝ) (hw : ∀ x ∈ S, 0 ≤ weight x) :
    (∑ x ∈ S, p x *
      (weight x * (1 / (p x * sourceLogCapacity b (p x))) * (max 0 (d x - a x)) ^ 2 -
        sourceParentMark weight (parent x) * sourceExactH (p x) * (max 0 (-d x)) ^ 2)) ≤ 0 := by
  have he : (∑ x ∈ S, p x *
      (weight x * (1 / (p x * sourceLogCapacity b (p x))) * (max 0 (d x - a x)) ^ 2 -
        sourceParentMark weight (parent x) * sourceExactH (p x) * (max 0 (-d x)) ^ 2)) =
      ∑ x ∈ S, (weight x * ((max 0 (d x - a x)) ^ 2 / sourceLogCapacity b (p x)) -
        sourceParentMark weight (parent x) * (p x * sourceExactH (p x) * (max 0 (-d x)) ^ 2)) := by
    apply sum_congr rfl
    intro x hx
    exact scale_capacity (h.probability_pos (fun y hy => (hactivity y hy).1) hx).ne'
  rw [he]
  exact h.exact_negative_capacity_budget hactivity weight hw

#print axioms SourceMessages.exact_positive_capacity_budget
#print axioms SourceMessages.exact_negative_capacity_budget
#print axioms SourceMessages.exact_positive_capacity_budget_scaled
#print axioms SourceMessages.exact_negative_capacity_budget_scaled

end ForestUnimodality
