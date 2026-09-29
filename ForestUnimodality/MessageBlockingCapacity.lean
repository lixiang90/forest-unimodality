import ForestUnimodality.MessageWeightedResponse
import ForestUnimodality.SourceOddsCapacity

/-! The blocking price is evaluated at the actual parent message. No child
degree bound and no replacement by an independent worst parent is used. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

theorem SourceMessages.weighted_blocking_capacity_budget
    {G : SimpleGraph V} {S : Finset V} {activity a : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0<activity x ∧ activity x≤b)
    (weight : V → ℝ) (hw : ∀ x ∈ S, 0≤weight x) :
    (∑x∈S, p x *
      (weight x*(heterogeneousMarginal G S activity x/p x)*
        ((a x-d x)^2/sourceOddsCapacity b (sourceLogCapacity b (p x))) -
       (1-heterogeneousMarginal G S activity x/p x)*
         sourceParentMark weight (parent x)*(1-p x)*d x^2))≤0 := by
  have hlocal:=sum_le_sum (s:=S) (fun x hx=>mul_le_mul_of_nonneg_left
    (h.blocking_response_capacity hactivity hx)
    (mul_nonneg
      (heterogeneousMarginal_mem_Icc G S activity (fun y hy=>(hactivity y hy).1.le) x).1
      (hw x hx)))
  rw [h.sum_parent_mark_eq (fun x=>heterogeneousMarginal G S activity x*weight x)
    (fun x=>p x*(1-p x)*d x^2)] at hlocal
  have he : (∑x∈S, p x *
      (weight x*(heterogeneousMarginal G S activity x/p x)*
        ((a x-d x)^2/sourceOddsCapacity b (sourceLogCapacity b (p x))) -
       (1-heterogeneousMarginal G S activity x/p x)*
         sourceParentMark weight (parent x)*(1-p x)*d x^2)) =
      (∑x∈S, (heterogeneousMarginal G S activity x*weight x)*
        ((a x-d x)^2/sourceOddsCapacity b (sourceLogCapacity b (p x)))) -
      ∑x∈S, sourceParentMark (fun y=>heterogeneousMarginal G S activity y*weight y)
        (parent x)*(p x*(1-p x)*d x^2) := by
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro x hx
    have hp:=(h.probability_pos (fun y hy=>(hactivity y hy).1) hx).ne'
    have hr : heterogeneousMarginal G S activity x/p x=
        1-sourceParentMass G S activity (parent x) := by
      rw [h.marginal x hx]
      exact mul_div_cancel_left₀ _ hp
    rw [hr,h.marginal x hx]
    cases hh : parent x <;> simp only [sourceParentMark,sourceParentMass] <;> ring
  rw [he]
  exact sub_nonpos.mpr hlocal

#print axioms SourceMessages.weighted_blocking_capacity_budget
end ForestUnimodality
