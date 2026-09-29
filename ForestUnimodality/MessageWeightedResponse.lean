import ForestUnimodality.ForestSourceCapacity

/-! The response multiplier may depend on the actual vertex message and may
have either sign. Parent and child terms use the same parent weight. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

theorem SourceMessages.sum_parent_mark_eq {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) (weight cost : V → ℝ) :
    (∑ x ∈ S, weight x * ∑ y ∈ sourceChildren S parent x, cost y) =
      ∑ y ∈ S, sourceParentMark weight (parent y) * cost y := by
  classical
  simp only [sourceChildren, sum_filter, mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro y hy
  cases hp : parent y with
  | none => simp [sourceParentMark]
  | some x =>
      have hx := (h.parent_mem y hy x hp).1
      simp [sourceParentMark, hx]

theorem SourceMessages.weighted_response_zero {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) (weight : V → ℝ) :
    (∑ x ∈ S, (heterogeneousMarginal G S activity x * weight x * (d x - a x) +
      sourceParentMark (fun y => heterogeneousMarginal G S activity y * weight y)
        (parent x) * (p x * d x))) = 0 := by
  rw [sum_add_distrib, ← h.sum_parent_mark_eq
    (fun x => heterogeneousMarginal G S activity x * weight x) (fun x => p x * d x),
    ← sum_add_distrib]
  apply sum_eq_zero
  intro x hx
  have hr := h.response x hx
  unfold sourceChildResponse at hr
  rw [hr]
  ring

theorem SourceMessages.retained_weighted_response_zero
    {G : SimpleGraph V} {S : Finset V} {activity a : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d)
    (hp : ∀ x ∈ S, p x ≠ 0) (weight : V → ℝ) :
    (∑ x ∈ S, p x *
      ((heterogeneousMarginal G S activity x / p x) * weight x * (d x - a x) +
        (1 - heterogeneousMarginal G S activity x / p x) *
          sourceParentMark weight (parent x) * d x)) = 0 := by
  rw [← h.weighted_response_zero weight]
  apply sum_congr rfl
  intro x hx
  have hr : heterogeneousMarginal G S activity x / p x =
      1 - sourceParentMass G S activity (parent x) := by
    rw [h.marginal x hx]
    field_simp [hp x hx]
  rw [hr, h.marginal x hx]
  cases he : parent x <;> simp only [sourceParentMark, sourceParentMass] <;> ring

/-- The message-dependent multiplier identity used in the finite-order
source refinement, with no sign condition on the multiplier function. -/
theorem SourceMessages.message_response_zero
    {G : SimpleGraph V} {S : Finset V} {activity : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity (fun _ => 1) parent p d)
    (hactivity : ∀ x ∈ S, 0 < activity x) (τ : ℝ → ℝ) :
    (∑ x ∈ S, p x *
      ((heterogeneousMarginal G S activity x / p x) * τ (p x) * (d x - 1) +
        (1 - heterogeneousMarginal G S activity x / p x) *
          sourceParentMark (fun y => τ (p y)) (parent x) * d x)) = 0 :=
  h.retained_weighted_response_zero
    (fun _ hx => (h.probability_pos hactivity hx).ne') (fun x => τ (p x))

#print axioms SourceMessages.sum_parent_mark_eq
#print axioms SourceMessages.weighted_response_zero
#print axioms SourceMessages.retained_weighted_response_zero
#print axioms SourceMessages.message_response_zero

end ForestUnimodality
