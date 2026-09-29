import ForestUnimodality.IndependentCountLaplace
import ForestUnimodality.SourceSizeBound

/-! The finite list of tilt choices does not discretize the activity.
Each fixed tilt gives a concave rate across the whole probability interval. -/
namespace ForestUnimodality.AffineLaplace
open Set

theorem decayIntegral_nonneg {C u : ℝ} (hC : 0 < C) (hu : 0 ≤ u) :
    0 ≤ decayIntegral C u := by
  apply div_nonneg _ hC.le
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))

theorem decayIntegral_le {C u : ℝ} (hC : 0 < C) (_hu : 0 ≤ u) :
    decayIntegral C u ≤ u := by
  apply (div_le_iff₀ hC).mpr
  have he := Real.add_one_le_exp (-C*u)
  nlinarith

noncomputable def tailRate (A C density α u q : ℝ) : ℝ :=
  q*decayIntegral C u + α*Real.log (1-q+q*Real.exp (-u)) -
    A/C*(2*q/density-1)*(u-decayIntegral C u)

theorem tiltBase_pos {u q : ℝ} (hu : 0 ≤ u) (hq : q ∈ Icc (0 : ℝ) 1) :
    0 < 1-q+q*Real.exp (-u) := by
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
  have hp := Real.exp_pos (-u)
  have hc := mul_nonneg (sub_nonneg.mpr hq.2) (sub_nonneg.mpr he)
  nlinarith

theorem concaveOn_tailRate (A C density : ℝ) {α u : ℝ} (hα : 0 ≤ α) (hu : 0 ≤ u) :
    ConcaveOn ℝ (Icc 0 1) (tailRate A C density α u) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy s t hs ht hst
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2
    (tiltBase_pos hu hx) (tiltBase_pos hu hy) hs ht hst
  simp only [smul_eq_mul] at hlog ⊢
  have he : s*(1-x+x*Real.exp (-u)) + t*(1-y+y*Real.exp (-u)) =
      1-(s*x+t*y)+(s*x+t*y)*Real.exp (-u) := by nlinarith [hst]
  rw [he] at hlog
  have h := mul_le_mul_of_nonneg_left hlog hα
  have ht' : t=1-s := by linarith
  subst t
  unfold tailRate
  simp only [div_eq_mul_inv]
  nlinarith only [h]

/-- Both endpoint bounds apply to every real probability in between. -/
theorem tailRate_lower_of_endpoints (A C density : ℝ) {α u lo hi q rate : ℝ}
    (hα : 0 ≤ α) (hu : 0 ≤ u) (hlo : 0 ≤ lo) (hhi : hi ≤ 1) (hlohi : lo ≤ hi)
    (hrlo : rate ≤ tailRate A C density α u lo)
    (hrhi : rate ≤ tailRate A C density α u hi) (hq : q ∈ Icc lo hi) :
    rate ≤ tailRate A C density α u q := by
  have hc := (concaveOn_tailRate A C density hα hu).subset
    (show Icc lo hi ⊆ Icc (0 : ℝ) 1 from fun _ hx => ⟨hlo.trans hx.1,hx.2.trans hhi⟩)
    (convex_Icc _ _)
  exact AnalyticInterval.lower_of_concave_endpoints hlohi hc hrlo hrhi hq

#print axioms concaveOn_tailRate
#print axioms tailRate_lower_of_endpoints
end ForestUnimodality.AffineLaplace

namespace ForestUnimodality
open Set
variable {V : Type*} [DecidableEq V]

theorem hardCoreAvailableMean_nonneg (G : SimpleGraph V) (S B : Finset V)
    {z : ℝ} (hz : 0 ≤ z) : 0 ≤ hardCoreAvailableMean G S B z := by
  unfold hardCoreAvailableMean
  exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun m _ =>
    mul_nonneg (hardCoreLayerWeight_nonneg G S B hz j m) (Nat.cast_nonneg m)

/-- The source proof supplies a bound on the entire fixed-B tilt path;
the density bound and endpoint rate then give a tail estimate at the same m. -/
theorem IsMaximumMarginalIndependentOn.lowerTail_le_rate
    {G : SimpleGraph V} {S B : Finset V} {z ρ A C α u rate : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hρ : 0 < ρ) (hρq : ρ ≤ z/(1+z))
    (hA : 0 ≤ A) (hC : 0 < C) (hu : 0 ≤ u)
    (hdensity : ρ*(S.card : ℝ) ≤ hardCoreMean G S z)
    (hsource : ∀ t ∈ Icc 0 u,
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J => ((J ∩ B).card : ℝ)) ≤ A*(B.card : ℝ) +
        C*heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t)))
          (fun J => ((J ∩ B).card : ℝ)))
    (hrate : rate ≤ AffineLaplace.tailRate A C ρ α u (z/(1+z))) :
    hardCoreAvailableLowerTail G S B z (α*hardCoreAvailableMean G S B z) ≤
      Real.exp (-rate*hardCoreAvailableMean G S B z) := by
  have h := hardCoreAvailableLowerTail_le_exp_affine G S B hB.subset hB.independent
    hz hu hC hsource (α*hardCoreAvailableMean G S B z)
  have hcard := hB.card_le_available_of_density hG hz hρ hρq hdensity
  have hcoef : 0 ≤ A/C*(u-AffineLaplace.decayIntegral C u) :=
    mul_nonneg (div_nonneg hA hC.le) (sub_nonneg.mpr (AffineLaplace.decayIntegral_le hC hu))
  have hsize := mul_le_mul_of_nonneg_left hcard hcoef
  have hm := hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz
  have hrate' := mul_le_mul_of_nonneg_right hrate (hardCoreAvailableMean_nonneg G S B hz.le)
  apply h.trans
  apply Real.exp_le_exp.mpr
  rw [hm]
  unfold AffineLaplace.tailRate at hrate'
  simp only [div_eq_mul_inv] at hsize hrate' ⊢
  nlinarith

#print axioms IsMaximumMarginalIndependentOn.lowerTail_le_rate
end ForestUnimodality
