import ForestUnimodality.NonnegativeSourceLibrary
import ForestUnimodality.FixedIndependentFlow

/-! Uniform bounds on the same original-B tilt, including the full count
and the non-independent complement. No maximum-set reselection is used. -/
namespace ForestUnimodality.FixedIndependentTilt
open Finset Set
variable {V : Type*} [DecidableEq V]

theorem uniform_variance_caps (i : Fin 16) (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S B : Finset V) (hBS : B⊆S) {z t m beta gamma : ℝ}
    (hz : 0<z) (hzb : z≤((NonnegativeSourceLibrary.parameters i).b:ℝ)) (ht : 0≤t)
    (hBcard : (B.card:ℝ)≤m*beta) (hScard : (S.card:ℝ)≤m*gamma)
    (hCcard : ((S\B).card:ℝ)≤m*beta) :
    let M : ℝ := (NonnegativeSourceLibrary.parameters i).A
    markedVariance G S B z t≤m*(M*beta) ∧
    FiniteTilt.variance (independentSubsets G S) (weight B z (z*Real.exp (-t)))
      (fun J=>(J.card:ℝ))≤m*(M*gamma) ∧
    complementVariance G S B z t≤m*(M*beta) := by
  dsimp only
  let P := NonnegativeSourceLibrary.parameters i
  have hact : ∀x∈S, 0 ≤ independentTiltActivities B z (Real.exp (-t)) x ∧
      independentTiltActivities B z (Real.exp (-t)) x≤(P.b:ℝ) := by
    intro x _
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
    unfold independentTiltActivities
    split_ifs
    · exact ⟨by positivity,(by nlinarith : Real.exp (-t)*z≤z).trans hzb⟩
    · exact ⟨hz.le,hzb⟩
  have hA := (NonnegativeSource.Parameters.check_sound (NonnegativeSourceLibrary.parameters_checked i)).A_nonneg
  have hb := NonnegativeSourceLibrary.actual_variance i G hG S B hBS _ hact
  have hs := NonnegativeSourceLibrary.actual_variance i G hG S S subset_rfl _ hact
  have hc := NonnegativeSourceLibrary.actual_variance i G hG S (S\B) sdiff_subset _ hact
  have hbi : (NonnegativeSourceLibrary.parameters i).A*(B.card:ℝ)≤
      m*((NonnegativeSourceLibrary.parameters i).A*beta) := by
    nlinarith [mul_le_mul_of_nonneg_left hBcard hA]
  have hsi : (NonnegativeSourceLibrary.parameters i).A*(S.card:ℝ)≤
      m*((NonnegativeSourceLibrary.parameters i).A*gamma) := by
    nlinarith [mul_le_mul_of_nonneg_left hScard hA]
  have hci : (NonnegativeSourceLibrary.parameters i).A*((S\B).card:ℝ)≤
      m*((NonnegativeSourceLibrary.parameters i).A*beta) := by
    nlinarith [mul_le_mul_of_nonneg_left hCcard hA]
  have hins : inside B=(fun J : Finset V=>((J∩B).card:ℝ)) := rfl
  have hfull : ∀J∈independentSubsets G S, ((J∩S).card:ℝ)=(J.card:ℝ) := by
    intro J hJ
    rw [Finset.inter_eq_left.mpr (mem_independentSubsets.mp hJ).1]
  have hcomp : ∀J∈independentSubsets G S, ((J∩(S\B)).card:ℝ)=outside B J := by
    intro J hJ
    have he : J∩(S\B)=J\B := by
      ext x
      simp only [Finset.mem_inter,Finset.mem_sdiff]
      exact ⟨fun h=>⟨h.1,h.2.2⟩,fun h=>⟨h.1,(mem_independentSubsets.mp hJ).1 h.1,h.2⟩⟩
    rw [he]; rfl
  simp only [heterogeneousVariance,←weight_eq_heterogeneous] at hb hs hc
  rw [finite_variance_congr _ _ _ _ hfull] at hs
  rw [finite_variance_congr _ _ _ _ hcomp] at hc
  refine ⟨?_,hs.trans hsi,?_⟩
  · simpa only [markedVariance,hins] using hb.trans hbi
  · exact hc.trans hci

theorem coarse_totalMean_on_step (G : SimpleGraph V) (S B : Finset V)
    {z start finish m U VB VK eta cap : ℝ}
    (hz : 0<z) (horder : start≤finish) (hm : 0≤m)
    (hVB : 0≤VB) (hVK : 0≤VK) (heta : 0≤eta) (hquad : VB*VK≤eta^2)
    (hstart : totalMean G S B z start≤m*U)
    (hmarked : ∀t∈Icc start finish, markedVariance G S B z t≤m*VB)
    (hfull : ∀t∈Icc start finish,
      FiniteTilt.variance (independentSubsets G S) (weight B z (z*Real.exp (-t)))
        (fun J=>(J.card:ℝ))≤m*VK)
    (hglobal : ∀t∈Icc start finish, totalMean G S B z t≤m*cap) :
    ∀t∈Icc start finish, totalMean G S B z t≤m*min (U+eta*(finish-start)) cap := by
  have hsqrt : Real.sqrt (VB*VK)≤eta := by
    have hs := Real.sq_sqrt (mul_nonneg hVB hVK)
    nlinarith [Real.sqrt_nonneg (VB*VK)]
  have hd (t : ℝ) (ht : t∈Icc start finish) : deriv (totalMean G S B z) t≤m*eta :=
    (totalMean_cauchy_drift G S B hz hm hVB hVK (hmarked t ht) (hfull t ht)).trans
      (mul_le_mul_of_nonneg_left hsqrt hm)
  have hc := PiecewiseFlowLaplace.whole_step_upper horder
    (fun t _=>(hasDerivAt_totalMean G S B hz t).differentiableAt.hasDerivAt) hd hstart
  intro t ht
  have hh := hc t ht
  rw [max_eq_right (mul_nonneg hm heta)] at hh
  by_cases hmin : U+eta*(finish-start)≤cap
  · rw [min_eq_left hmin]
    nlinarith
  · rw [min_eq_right (le_of_not_ge hmin)]
    exact hglobal t ht

#print axioms uniform_variance_caps
#print axioms coarse_totalMean_on_step
end ForestUnimodality.FixedIndependentTilt
