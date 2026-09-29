import ForestUnimodality.FixedIndependentFlow
import ForestUnimodality.TiltedSourceDomain
import ForestUnimodality.SourceSizeBound

/-! Cardinality and mean bounds normalized by the original available mean.
The same independent set is retained at every later time. -/
namespace ForestUnimodality.FixedIndependentTilt
open Finset Set
variable {V : Type*} [DecidableEq V]

theorem initial_normalized_bounds {G : SimpleGraph V} {S B : Finset V}
    {z rho qa qb : ℝ} (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hrho : 0<rho) (hrhoq : rho≤z/(1+z))
    (hq : z/(1+z)∈Icc qa qb) (hdensity : rho*(S.card:ℝ)≤hardCoreMean G S z) :
    let m := hardCoreAvailableMean G S B z
    0≤m ∧ m≤(B.card:ℝ) ∧
    (S.card:ℝ)≤(2*qb/rho)*m ∧
    (B.card:ℝ)≤(2*qb/rho-1)*m ∧
    ((S\B).card:ℝ)≤(2*qb/rho-1)*m ∧
    qa*m≤markedMean G S B z 0 ∧ totalMean G S B z 0≤2*qb*m := by
  dsimp only
  let m := hardCoreAvailableMean G S B z
  have hm : 0≤m := hardCoreAvailableMean_nonneg G S B hz.le
  have hqp : 0<z/(1+z) := by positivity
  have hmass := hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz
  have hcard := hardCoreOccupiedMass_le_activity_card G S B hB.subset hz
  rw [hmass] at hcard
  have hmcard : m≤(B.card:ℝ) := (mul_le_mul_iff_right₀ hqp).mp hcard
  have hhalf := hB.half_mean hG.isBipartite
  rw [hmass] at hhalf
  have hqm := mul_le_mul_of_nonneg_right hq.2 hm
  have hmean : hardCoreMean G S z≤2*qb*m := by
    dsimp [m] at hqm ⊢
    linarith
  have hn : (S.card:ℝ)≤(2*qb/rho)*m := by
    apply (mul_le_mul_iff_right₀ hrho).mp
    have hid : rho*((2*qb/rho)*m)=2*qb*m := by field_simp
    rw [hid]
    exact hdensity.trans hmean
  have hb := hB.card_le_available_of_density hG hz hrho hrhoq hdensity
  have hbeta : 2*(z/(1+z))/rho-1≤2*qb/rho-1 := by gcongr; exact hq.2
  have hb' : (B.card:ℝ)≤(2*qb/rho-1)*m :=
    hb.trans (mul_le_mul_of_nonneg_right hbeta hm)
  have hcomp : ((S\B).card:ℝ)=(S.card:ℝ)-(B.card:ℝ) := by
    rw [card_sdiff_of_subset hB.subset,Nat.cast_sub (Finset.card_le_card hB.subset)]
  have hmu0 : totalMean G S B z 0=hardCoreMean G S z := by
    unfold totalMean
    rw [weight_eq_heterogeneous]
    have ha : independentTiltActivities B z (Real.exp (-(0:ℝ)))=(fun _=>z) := by
      funext x
      simp [independentTiltActivities]
    change heterogeneousMean G S (independentTiltActivities B z (Real.exp (-(0:ℝ)))) (fun J=>(J.card:ℝ))=_
    rw [ha,heterogeneousMean_common_card]
  refine ⟨hm,hmcard,hn,hb',?_,?_,?_⟩
  · rw [hcomp]
    nlinarith
  · rw [markedMean_zero,hmass]
    exact mul_le_mul_of_nonneg_right hq.1 hm
  · rw [hmu0]
    exact hmean

theorem heterogeneous_totalMean_le_probability_card (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (activity : V→ℝ) {b : ℝ}
    (hactivity : ∀x∈S,0<activity x ∧ activity x≤b) :
    heterogeneousMean G S activity (fun J=>(J.card:ℝ))≤b/(1+b)*(S.card:ℝ) := by
  obtain ⟨parent,p,d,hm,_,_⟩ := exists_forest_source_messages_moments G hG S activity
    (fun _=>1) (fun x hx=>(hactivity x hx).1.le)
  have hmean := heterogeneousMean_marked_eq_sum_marginals G S activity (fun _=>1)
  have he : markedSum (fun _:V=>1)=(fun J=>(J.card:ℝ)) := by
    funext J
    simp [markedSum]
  rw [he] at hmean
  rw [hmean]
  have hsum := sum_le_sum (s:=S) (f:=heterogeneousMarginal G S activity)
    (g:=fun _=>b/(1+b)) (fun x hx=>
      (hm.marginal_le_probability (fun y hy=>(hactivity y hy).1.le) hx).trans
      (hm.probability_le_local_bound (fun y hy=>(hactivity y hy).1) (hactivity x hx).2 hx))
  simpa only [mul_one,sum_const,nsmul_eq_mul,mul_comm] using hsum

theorem totalMean_global_cap (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V)
    {z b t m gamma : ℝ} (hz : 0<z) (hzb : z≤b) (ht : 0≤t)
    (hcard : (S.card:ℝ)≤gamma*m) :
    totalMean G S B z t≤(b/(1+b)*gamma)*m := by
  have hact : ∀x∈S,0 < independentTiltActivities B z (Real.exp (-t)) x ∧
      independentTiltActivities B z (Real.exp (-t)) x≤b := by
    intro x _
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
    unfold independentTiltActivities
    split_ifs
    · exact ⟨mul_pos (Real.exp_pos _) hz,(by nlinarith : Real.exp (-t)*z≤z).trans hzb⟩
    · exact ⟨hz,hzb⟩
  have hh := heterogeneous_totalMean_le_probability_card G hG S _ hact
  have hb : 0<b := hz.trans_le hzb
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hcard (by positivity : 0≤b/(1+b)))
  simpa only [totalMean,weight_eq_heterogeneous,heterogeneousMean,mul_assoc] using hh'

#print axioms initial_normalized_bounds
#print axioms heterogeneous_totalMean_le_probability_card
#print axioms totalMean_global_cap
end ForestUnimodality.FixedIndependentTilt
