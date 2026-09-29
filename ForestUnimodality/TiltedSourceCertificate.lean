import ForestUnimodality.TiltedSourceDomain
import ForestUnimodality.FixedIndependentTilt

/-! Independent-mark sources with two actual activity caps. No positive
lower activity bound is needed, and the same marked set is retained. -/
namespace ForestUnimodality
open Finset

structure TiltedSourceParameters where
  C : ℝ
  positivePrice : ℝ→ℝ
  negativePrice : ℝ→ℝ

def TiltedSourceParameters.Admissible (P : TiltedSourceParameters) : Prop :=
  (∀a, 0≤P.positivePrice a) ∧ (∀a, 0≤P.negativePrice a)

noncomputable def tiltedSourceRow (P : TiltedSourceParameters) (cap : ℝ→ℝ)
    (a pa p r d : ℝ) : ℝ :=
  P.C*r*a-r*(1-p)*d^2+
  P.positivePrice a*(1/(p*sourceLogCapacity (cap a) p))*(max 0 (a-d))^2-
  P.positivePrice pa*(1-p/2)*(max 0 d)^2+
  P.negativePrice a*(1/(p*sourceLogCapacity (cap a) p))*(max 0 (d-a))^2-
  P.negativePrice pa*(1-p/2)*(max 0 (-d))^2

def TiltedSourceRowValid (P : TiltedSourceParameters) (cap : ℝ→ℝ) : Prop :=
  ∀a pa, SourceMarkState a pa → ∀p r d, 0<p → p≤cap a/(1+cap a) →
    1/(1+cap pa*(1-p))≤r → r≤1 → (p=cap a/(1+cap a) → d=a) →
    0≤tiltedSourceRow P cap a pa p r d

variable {V : Type*} [DecidableEq V]

theorem forest_tilted_source_variance_of_scalar_certificate
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V)
    (hB : G.IsIndepSet (B:Set V)) (activity : V→ℝ) (cap : ℝ→ℝ)
    (hcap : ∀a, 0<cap a)
    (hactivity : ∀x∈S, 0<activity x ∧ activity x≤cap (sourceIndicator B x))
    (P : TiltedSourceParameters) (hP : P.Admissible) (hvalid : TiltedSourceRowValid P cap) :
    heterogeneousVariance G S activity (fun J=>((J∩B).card:ℝ)) ≤
      P.C*heterogeneousMean G S activity (fun J=>((J∩B).card:ℝ)) := by
  obtain ⟨parent,p,d,hm,hmean,hvar⟩ := exists_forest_source_messages_moments G hG S activity
    (sourceIndicator B) (fun x hx=>(hactivity x hx).1.le)
  have hact : ∀x∈S, 0<activity x := fun x hx=>(hactivity x hx).1
  have hp : ∀x∈S, 0<p x := fun x hx=>hm.probability_pos hact hx
  have hrow : 0≤∑x∈S,p x*tiltedSourceRow P cap (sourceIndicator B x)
      (sourceParentMark (sourceIndicator B) (parent x)) (p x)
      (heterogeneousMarginal G S activity x/p x) (d x) := by
    apply sum_nonneg
    intro x hx
    apply mul_nonneg (hp x hx).le
    have hr := hm.retention_bounds_local_parent (hcap (sourceParentMark (sourceIndicator B) (parent x))) hact hx (fun y hy=>by
      simpa only [hy,sourceParentMark] using (hactivity y (hm.parent_mem x hx y hy).1).2)
    exact hvalid _ _ (hm.independent_mark_state hB hx) _ _ _ (hp x hx)
      (hm.probability_le_local_bound hact (hactivity x hx).2 hx) hr.1 hr.2
      (hm.response_at_local_probability_endpoint hact (hactivity x hx).2 hx)
  have hpos := hm.positive_variable_capacity_budget (fun x=>cap (sourceIndicator B x))
    hactivity P.positivePrice hP.1
  have hneg := hm.negative_variable_capacity_budget (fun x=>cap (sourceIndicator B x))
    hactivity P.negativePrice hP.2
  have he : (∑x∈S,p x*tiltedSourceRow P cap (sourceIndicator B x)
      (sourceParentMark (sourceIndicator B) (parent x)) (p x)
      (heterogeneousMarginal G S activity x/p x) (d x)) =
      P.C*(∑x∈S,heterogeneousMarginal G S activity x*sourceIndicator B x)-
      (∑x∈S,heterogeneousMarginal G S activity x*(1-p x)*d x^2)+
      (∑x∈S,(P.positivePrice (sourceIndicator B x)*
        ((max 0 (sourceIndicator B x-d x))^2/sourceLogCapacity (cap (sourceIndicator B x)) (p x))-
        P.positivePrice (sourceParentMark (sourceIndicator B) (parent x))*p x*(1-p x/2)*(max 0 (d x))^2))+
      (∑x∈S,(P.negativePrice (sourceIndicator B x)*
        ((max 0 (d x-sourceIndicator B x))^2/sourceLogCapacity (cap (sourceIndicator B x)) (p x))-
        P.negativePrice (sourceParentMark (sourceIndicator B) (parent x))*p x*(1-p x/2)*(max 0 (-d x))^2)) := by
    simp only [mul_sum,←sum_sub_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro x hx
    unfold tiltedSourceRow
    by_cases hc : sourceLogCapacity (cap (sourceIndicator B x)) (p x)=0
    · simp only [hc,mul_zero,div_zero,mul_zero,zero_mul]
      field_simp [(hp x hx).ne']
      ring
    · field_simp [(hp x hx).ne',hc]
      ring
  rw [he,←hvar,←heterogeneousMean_marked_eq_sum_marginals] at hrow
  have hind : markedSum (sourceIndicator B)=(fun J:Finset V=>((J∩B).card:ℝ)) :=
    funext (markedSum_sourceIndicator B)
  rw [hind] at hrow
  linarith

noncomputable def tiltedMarkCap (b0 b1 a : ℝ) : ℝ := if a=1 then b1 else b0

theorem forest_fixed_independent_tilt_variance
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V)
    (hB : G.IsIndepSet (B:Set V)) {z b0 b1 start : ℝ}
    (hz : 0<z) (hb0 : 0<b0) (hb1 : 0<b1) (hzcap : z≤b0)
    (hstart : z*Real.exp (-start)≤b1)
    (P : TiltedSourceParameters) (hP : P.Admissible)
    (hvalid : TiltedSourceRowValid P (tiltedMarkCap b0 b1)) :
    ∀t≥start, FixedIndependentTilt.markedVariance G S B z t≤
      P.C*FixedIndependentTilt.markedMean G S B z t := by
  intro t ht
  have hact : ∀x∈S, 0 < independentTiltActivities B z (Real.exp (-t)) x ∧
      independentTiltActivities B z (Real.exp (-t)) x≤tiltedMarkCap b0 b1 (sourceIndicator B x) := by
    intro x _
    by_cases hx : x∈B
    · simp only [independentTiltActivities,sourceIndicator,hx,if_true,tiltedMarkCap]
      refine ⟨mul_pos (Real.exp_pos _) hz,?_⟩
      have he := Real.exp_le_exp.mpr (show -t≤-start by linarith)
      nlinarith [mul_le_mul_of_nonneg_left he hz.le]
    · simp only [independentTiltActivities,sourceIndicator,hx,if_false,tiltedMarkCap,
        zero_ne_one,if_false]
      exact ⟨hz,hzcap⟩
  have hh := forest_tilted_source_variance_of_scalar_certificate G hG S B hB
    (independentTiltActivities B z (Real.exp (-t))) (tiltedMarkCap b0 b1)
    (fun a=>by unfold tiltedMarkCap; split_ifs <;> assumption) hact P hP hvalid
  unfold FixedIndependentTilt.markedVariance FixedIndependentTilt.markedMean
  rw [FixedIndependentTilt.weight_eq_heterogeneous]
  unfold FixedIndependentTilt.inside
  simpa only [heterogeneousVariance,heterogeneousMean] using hh

#print axioms forest_tilted_source_variance_of_scalar_certificate
#print axioms forest_fixed_independent_tilt_variance
end ForestUnimodality
