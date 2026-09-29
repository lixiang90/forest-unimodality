import ForestUnimodality.FlowUniformBounds
import ForestUnimodality.PiecewiseFlowZeroSlope

/-! The order of the two-variable refinement is explicit: a coarse cap
gives a preliminary occupation floor, then a complement drift gives a fine
cap, and only that established fine cap is used in the final variance source. -/
namespace ForestUnimodality.FixedIndependentTilt
open Set
variable {V : Type*} [DecidableEq V]

theorem scaled_min_upper {x m a b : ℝ} (ha : x≤m*a) (hb : x≤m*b) :
    x≤m*min a b := by
  rcases le_total a b with h|h
  · rw [min_eq_left h]; exact ha
  · rw [min_eq_right h]; exact hb

theorem marked_endpoint_of_affine (G : SimpleGraph V) (S B : Finset V)
    {z start finish m L D C next : ℝ} (hz : 0<z) (horder : start≤finish)
    (hm : 0≤m) (hC : 0≤C) (hstart : m*L≤markedMean G S B z start)
    (hvar : ∀t∈Icc start finish, markedVariance G S B z t≤m*D+C*markedMean G S B z t)
    (hnext : next≤max 0 (PiecewiseFlowZeroSlope.endLower L D C (finish-start))) :
    m*next≤markedMean G S B z finish := by
  have he := PiecewiseFlowZeroSlope.affine_endpoint horder hC
    (fun t _=>hasDerivAt_markedMean G S B hz t) hvar hstart
  rw [PiecewiseFlowZeroSlope.endLower_scale] at he
  have hh : m*max 0 (PiecewiseFlowZeroSlope.endLower L D C (finish-start))≤
      markedMean G S B z finish := by
    rw [←PiecewiseFlowZeroSlope.max_zero_mul hm]
    exact max_le (markedMean_nonneg G S B hz finish) he
  exact (mul_le_mul_of_nonneg_left hnext hm).trans hh

theorem coupled_step (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V))
    {z start finish m L U coarse Dpre Cpre Lpre VB VK eta Vc qu fine Unext D C Lnext : ℝ}
    (hz : 0<z) (horder : start≤finish) (hm : 0≤m)
    (hstartW : m*L≤markedMean G S B z start) (hstartU : totalMean G S B z start≤m*U)
    (hcoarse : ∀t∈Icc start finish, totalMean G S B z t≤m*coarse)
    (hpreC : 0≤Cpre) (hLpre : 0≤Lpre)
    (hpreVar : ∀t∈Icc start finish, markedVariance G S B z t≤m*Dpre+Cpre*markedMean G S B z t)
    (hpre : Lpre≤max 0 (PiecewiseFlowZeroSlope.endLower L Dpre Cpre (finish-start)))
    (hVB : 0≤VB) (hVK : 0≤VK) (heta : 0≤eta) (hquad : VB*VK≤eta^2)
    (hvarB : ∀t∈Icc start finish, markedVariance G S B z t≤m*VB)
    (hvarK : ∀t∈Icc start finish,
      FiniteTilt.variance (independentSubsets G S) (weight B z (z*Real.exp (-t)))
        (fun J=>(J.card:ℝ))≤m*VK)
    (hqu : qu≤1) (hq : ∀t∈Icc start finish, logisticTilt z t≤qu)
    (hcomp : m*Lpre≤markedMean G S B z finish →
      ∀t∈Icc start finish, complementVariance G S B z t≤m*Vc)
    (hfine : min (min (U+eta*(finish-start)) coarse)
      (U+max 0 (Vc/4-(1-qu)*Lpre)*(finish-start))≤fine)
    (hUnext : min fine (U+(Vc/4-(1-qu)*Lpre)*(finish-start))≤Unext)
    (hC : 0≤C)
    (hfinalVar : (∀t∈Icc start finish, totalMean G S B z t≤m*fine) →
      ∀t∈Icc start finish, markedVariance G S B z t≤m*D+C*markedMean G S B z t)
    (hLnext : Lnext≤max 0 (PiecewiseFlowZeroSlope.endLower L D C (finish-start))) :
    (∀t∈Icc start finish, totalMean G S B z t≤m*fine) ∧
    totalMean G S B z finish≤m*Unext ∧ m*Lnext≤markedMean G S B z finish := by
  have hp := marked_endpoint_of_affine G S B hz horder hm hpreC hstartW hpreVar hpre
  have hcauchy := coarse_totalMean_on_step G S B hz horder hm hVB hVK heta hquad
    hstartU hvarB hvarK hcoarse
  have hd := totalMean_step_bounds G S B hBS hB hz horder hm hLpre hqu hstartU hp hq (hcomp hp)
  have hfin : ∀t∈Icc start finish, totalMean G S B z t≤m*fine := by
    intro t ht
    exact (scaled_min_upper (hcauchy t ht) (hd.2 t ht)).trans
      (mul_le_mul_of_nonneg_left hfine hm)
  refine ⟨hfin,?_,?_⟩
  · exact (scaled_min_upper (hfin finish ⟨horder,le_refl _⟩) hd.1).trans
      (mul_le_mul_of_nonneg_left hUnext hm)
  · exact marked_endpoint_of_affine G S B hz horder hm hC hstartW (hfinalVar hfin) hLnext

#print axioms marked_endpoint_of_affine
#print axioms coupled_step
end ForestUnimodality.FixedIndependentTilt
