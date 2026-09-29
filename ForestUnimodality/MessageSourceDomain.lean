import ForestUnimodality.MessageWeightedResponse
import ForestUnimodality.ForestSourcePhi

/-! The two-sided feasible parent-message interval comes from the same true
forest message system used by the variance and response identities. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

theorem SourceMessages.parent_probability_bounds
    {G : SimpleGraph V} {S : Finset V} {activity a : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0<activity x ∧ activity x≤b) {x : V} (hx : x∈S) :
    1-heterogeneousMarginal G S activity x/p x≤sourceParentMark p (parent x) ∧
      sourceParentMark p (parent x)≤b*(1-p x)/(1+b*(1-p x)) := by
  have hp:=(h.probability_pos (fun y hy=>(hactivity y hy).1) hx).ne'
  have hp1:=sub_pos.mpr (h.probability x hx).2
  have hb:=(hactivity x hx).1.trans_le (hactivity x hx).2
  have hden : 0<1+b*(1-p x) := by positivity
  have hr : heterogeneousMarginal G S activity x/p x=
      1-sourceParentMass G S activity (parent x) := by
    rw [h.marginal x hx]
    exact mul_div_cancel_left₀ _ hp
  rw [hr]
  cases hh : parent x with
  | none =>
      simp only [sourceParentMark,sourceParentMass,sub_zero,sub_self,le_refl,true_and]
      exact div_nonneg (mul_nonneg hb.le hp1.le) hden.le
  | some y =>
      have hy:=(h.parent_mem x hx y hh).1
      simp only [sourceParentMark,sourceParentMass,sub_sub_cancel]
      refine ⟨h.marginal_le_probability (fun z hz=>(hactivity z hz).1.le) hy,?_⟩
      have hxy : x∈sourceChildren S parent y := mem_filter.mpr ⟨hx,hh⟩
      have hodds : p y/(1-p y)≤b*(1-p x) := by
        rw [h.odds_eq hy]
        exact (mul_le_mul_of_nonneg_left (h.child_product_le_factor hxy)
          (hactivity y hy).1.le).trans
          (mul_le_mul_of_nonneg_right (hactivity y hy).2 hp1.le)
      have hh':=(div_le_iff₀ (sub_pos.mpr (h.probability y hy).2)).mp hodds
      apply (le_div_iff₀ hden).mpr
      nlinarith

#print axioms SourceMessages.parent_probability_bounds
end ForestUnimodality
