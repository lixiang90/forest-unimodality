import ForestUnimodality.BasicFlowNormalized
import ForestUnimodality.AffineSourceLaplaceRate

/-! Two whole analytic phases with one common initial activity parameter.
The normalized cardinality bound and initial mass retain their correlation.
The resulting rate is affine in q, so two endpoint bounds cover the interval. -/
namespace ForestUnimodality.CorrelatedTwoPhase
open Set Finset

noncomputable def rate (A C₁ C₂ rho u v q : ℝ) : ℝ :=
  PiecewiseFlowLaplace.integralLower q (A*(2*q/rho-1)) C₁ u +
    PiecewiseFlowLaplace.integralLower
      (PiecewiseFlowLaplace.endLower q (A*(2*q/rho-1)) C₁ u) 0 C₂ (v-u)

theorem rate_affine (A C₁ C₂ rho u v q : ℝ) :
    rate A C₁ C₂ rho u v q =
      (rate A C₁ C₂ rho u v 1-rate A C₁ C₂ rho u v 0)*q+
        rate A C₁ C₂ rho u v 0 := by
  unfold rate PiecewiseFlowLaplace.integralLower PiecewiseFlowLaplace.endLower
  ring

theorem rate_lower_of_endpoints {A C₁ C₂ rho u v lo hi q r : ℝ}
    (hq : q∈Icc lo hi)
    (hlo : r≤rate A C₁ C₂ rho u v lo)
    (hhi : r≤rate A C₁ C₂ rho u v hi) :
    r≤rate A C₁ C₂ rho u v q := by
  rw [rate_affine] at hlo hhi ⊢
  by_cases hs : 0≤rate A C₁ C₂ rho u v 1-rate A C₁ C₂ rho u v 0
  · nlinarith [mul_le_mul_of_nonneg_left hq.1 hs]
  · nlinarith [mul_le_mul_of_nonpos_left hq.2 (le_of_not_ge hs)]

variable {V : Type*} [DecidableEq V]

theorem actual_two_phase {G : SimpleGraph V} {S B : Finset V}
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V))
    {z m q D₁ D₂ C₁ C₂ u v retention : ℝ}
    (hz : 0<z) (hm : 0≤m) (hu : 0≤u) (huv : u≤v)
    (hC₁ : 0<C₁) (hC₂ : 0<C₂)
    (hstart : m*q≤hardCoreOccupiedMass G S B z)
    (hfirst : ∀t∈Icc 0 u,
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)) ≤ m*D₁+C₁*
      heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)))
    (hsecond : ∀t∈Icc u v,
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)) ≤ m*D₂+C₂*
      heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)))
    (hrt : 0≤retention) (htime : retention≤Real.exp (-v)) :
    hardCoreLayerLaplace G S B z retention ≤ Real.exp (-m*
      (PiecewiseFlowLaplace.integralLower q D₁ C₁ u +
       PiecewiseFlowLaplace.integralLower
        (PiecewiseFlowLaplace.endLower q D₁ C₁ u) D₂ C₂ (v-u))) := by
  let e := PiecewiseFlowLaplace.endLower q D₁ C₁ u
  let times : ℕ→ℝ := fun i=>if i=0 then 0 else if i=1 then u else v
  let lowers : ℕ→ℝ := fun i=>if i=0 then q else if i=1 then e else
    PiecewiseFlowLaplace.endLower e D₂ C₂ (v-u)
  let charges : ℕ→ℝ := fun i=>if i=0 then PiecewiseFlowLaplace.integralLower q D₁ C₁ u
    else PiecewiseFlowLaplace.integralLower e D₂ C₂ (v-u)
  let ds : ℕ→ℝ := fun i=>if i=0 then D₁ else D₂
  let cs : ℕ→ℝ := fun i=>if i=0 then C₁ else C₂
  have hv : ∀i<2, ∀t∈Icc (times i) (times (i+1)),
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)) ≤ m*ds i+cs i*
      heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)) := by
    intro i hi
    interval_cases i
    · simpa [times,ds,cs] using hfirst
    · simpa [times,ds,cs] using hsecond
  have hh := PiecewiseFlowLaplace.actual_laplace_chain_scaled G S B hBS hB hz hm
    times lowers charges ds cs ds cs 2 (by simp [times])
    (by simpa [lowers] using hstart)
    (by intro i hi; interval_cases i <;> simp [times,hu,huv])
    (by intro i hi; interval_cases i <;> simp [cs,hC₁,hC₂])
    (by intro i hi; interval_cases i <;> simp [cs,hC₁,hC₂]) hv hv
    (by intro i hi; interval_cases i <;> simp [lowers,ds,cs,times,e])
    (by intro i hi; interval_cases i <;> simp [charges,lowers,ds,cs,times,e])
    hrt (by simpa [times] using htime)
  simpa [sum_range_succ,charges,e] using hh

theorem actual_laplace (i : Fin 15) (j : Fin 36)
    {G : SimpleGraph V} {S B : Finset V}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    {rho u v lo hi retention r : ℝ}
    (hz : 0<z) (hρ : 0<rho) (hρq : rho≤z/(1+z))
    (hdensity : rho*(S.card:ℝ)≤hardCoreMean G S z)
    (hu : 0≤u) (huv : u≤v) (hrt : 0≤retention)
    (htime : retention≤Real.exp (-v))
    (hcap₁ : z≤((AffineSourceLibrary.domain i).b:ℝ))
    (hcap₂ : z≤((TiltedSourceLibrary.domain0 j).b:ℝ))
    (hmarked : z*Real.exp (-u)≤((TiltedSourceLibrary.domain1 j).b:ℝ))
    (hq : z/(1+z)∈Icc lo hi)
    (hlo : r≤rate (AffineSourceLibrary.parameters i).A
      (AffineSourceLibrary.parameters i).C (TiltedSourceLibrary.parameters j).C rho u v lo)
    (hhi : r≤rate (AffineSourceLibrary.parameters i).A
      (AffineSourceLibrary.parameters i).C (TiltedSourceLibrary.parameters j).C rho u v hi) :
    hardCoreLayerLaplace G S B z retention≤Real.exp (-r*hardCoreAvailableMean G S B z) := by
  let m := hardCoreAvailableMean G S B z
  let q := z/(1+z)
  let A : ℝ := (AffineSourceLibrary.parameters i).A
  let C₁ : ℝ := (AffineSourceLibrary.parameters i).C
  let C₂ : ℝ := (TiltedSourceLibrary.parameters j).C
  have hm : 0≤m := hardCoreAvailableMean_nonneg G S B hz.le
  have hA : 0≤A := (AffineSource.Parameters.check_sound (AffineSourceLibrary.parameters_checked i)).2.1
  have hC₁ : 0<C₁ := AffineSourceLibrary.C_pos i
  have hC₂ : 0<C₂ := (TiltedSource.Parameters.check_sound (TiltedSourceLibrary.parameters_checked j)).2
  have hc : (B.card:ℝ)≤m*(2*q/rho-1) := by
    simpa [m,q,mul_comm] using hB.card_le_available_of_density hG hz hρ hρq hdensity
  have hstart : m*q≤hardCoreOccupiedMass G S B z := by
    have he := hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz
    dsimp [m,q]
    nlinarith only [he]
  have hfirst (t : ℝ) (ht : t∈Icc 0 u) :
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)) ≤ m*(A*(2*q/rho-1))+C₁*
      heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)) := by
    have hh := AffineSourceLibrary.actual_tilt i G hG S B hB.subset hz hcap₁ t ht.1
    change _≤A*(B.card:ℝ)+C₁*_ at hh
    nlinarith [mul_le_mul_of_nonneg_left hc hA]
  have hsecond (t : ℝ) (ht : t∈Icc u v) :
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)) ≤ m*0+C₂*
      heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ)) := by
    have hh := TiltedSourceLibrary.actual_variance j G hG S B hB.independent hz hcap₂ hmarked ht.1
    have hins : FixedIndependentTilt.inside B=(fun J : Finset V=>((J∩B).card:ℝ)) := rfl
    simpa only [mul_zero,zero_add,C₂,FixedIndependentTilt.markedVariance,
      FixedIndependentTilt.markedMean,FixedIndependentTilt.weight_eq_heterogeneous,
      hins,heterogeneousVariance,heterogeneousMean] using hh
  have hh := actual_two_phase hB.subset hB.independent hz hm hu huv hC₁ hC₂ hstart
    hfirst hsecond hrt htime
  change hardCoreLayerLaplace G S B z retention≤Real.exp (-m*rate A C₁ C₂ rho u v q) at hh
  have hr := rate_lower_of_endpoints hq hlo hhi
  apply hh.trans
  apply Real.exp_le_exp.mpr
  change -m*rate A C₁ C₂ rho u v q≤-r*m
  nlinarith [mul_le_mul_of_nonneg_left hr hm]

#print axioms rate_affine
#print axioms rate_lower_of_endpoints
#print axioms actual_two_phase
#print axioms actual_laplace
end ForestUnimodality.CorrelatedTwoPhase
