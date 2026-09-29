import ForestUnimodality.ConstantSourceLaplace
import ForestUnimodality.LaplaceRateInterval
import ForestUnimodality.SourceSizeBound
import ForestUnimodality.NonnegativeSourceCertificate
import ForestUnimodality.SourceSelectionCertificate

/-! Mean-matched source budgets for one actual maximum-marginal independent
set. Density is an actual inequality at the same activity; no log-density
formula or reoptimization of the set along the tilt is presumed. -/
namespace ForestUnimodality.MeanMatchedSourceBudget
open Finset Set
variable {V : Type*} [DecidableEq V]

theorem reciprocal_variance_coefficient_antitone {qa q Cs : ℝ}
    (hqa : 0<qa) (hqq : qa≤q) (hCs : q≤2*Cs) :
    Cs/q^2-(1-q)/q≤Cs/qa^2-(1-qa)/qa := by
  have hq : 0<q := hqa.trans_le hqq
  have hmiddle : 0≤Cs*(q+qa)-qa*q := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hCs)
      (by linarith : 0≤q+qa),mul_nonneg hq.le (sub_nonneg.mpr hqq)]
  have hp := mul_nonneg (sub_nonneg.mpr hqq) hmiddle
  have he : (Cs/qa^2-(1-qa)/qa)-(Cs/q^2-(1-q)/q)=
      (q-qa)*(Cs*(q+qa)-qa*q)/(qa^2*q^2) := by field_simp; ring
  have hh : 0≤(q-qa)*(Cs*(q+qa)-qa*q)/(qa^2*q^2) := div_nonneg hp (by positivity)
  linarith

theorem density_le_probability_cap (G : SimpleGraph V) (S : Finset V)
    {z ρ : ℝ} (hz : 0<z) (hS : 0<S.card)
    (hdensity : ρ*(S.card:ℝ)≤hardCoreMean G S z) : ρ≤z/(1+z) := by
  have hupper := hardCoreOccupiedMass_le_activity_card G S S subset_rfl hz
  rw [←hardCoreMean_eq_sum_vertex_marginals] at hupper
  have hn : 0<(S.card:ℝ) := by exact_mod_cast hS
  by_contra hh
  have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hh) hn
  linarith

theorem available_mean_lower {G : SimpleGraph V} {S B : Finset V} {z ρ qb : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hρ : 0<ρ) (hqb : z/(1+z)≤qb) (N : ℕ) (hN : N≤S.card)
    (hdensity : ρ*(S.card:ℝ)≤hardCoreMean G S z) :
    ρ*N/(2*qb)≤hardCoreAvailableMean G S B z := by
  have hq : 0<z/(1+z) := by positivity
  have hqb0 := hq.trans_le hqb
  have hmass := hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz
  have hhalf := hB.half_mean hG.isBipartite
  rw [hmass] at hhalf
  have hn : (N:ℝ)≤S.card := by exact_mod_cast hN
  have hnρ := mul_le_mul_of_nonneg_left hn hρ.le
  have hm := hardCoreAvailableMean_nonneg G S B hz.le
  have hqmul := mul_le_mul_of_nonneg_right hqb hm
  apply (div_le_iff₀ (by positivity : 0<2*qb)).mpr
  nlinarith

theorem tilt_variance_of_density {G : SimpleGraph V} {S B : Finset V}
    {z b ρ qb A u v Cs : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hzb : z≤b) (hρ : 0<ρ) (hρq : ρ≤z/(1+z))
    (hqb : z/(1+z)≤qb) (hA : 0≤A) (hu : 0≤u) (hv : 0≤v)
    (hvalid : NonnegativeSourceRowValid b A u v)
    (hdensity : ρ*(S.card:ℝ)≤hardCoreMean G S z)
    (hCs : A*(2*qb/ρ-1)≤Cs) :
    ∀t≥0, heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
      (fun J=>((J∩B).card:ℝ))≤Cs*hardCoreAvailableMean G S B z := by
  intro t ht
  have hact : ∀x∈S,0 ≤ independentTiltActivities B z (Real.exp (-t)) x ∧
      independentTiltActivities B z (Real.exp (-t)) x≤b := by
    intro x _
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
    unfold independentTiltActivities
    split_ifs
    · exact ⟨mul_nonneg (Real.exp_pos _).le hz.le,(by nlinarith : Real.exp (-t)*z≤z).trans hzb⟩
    · exact ⟨hz.le,hzb⟩
  have hs := forest_independent_constant_source_variance G hG S B hB.subset
    (independentTiltActivities B z (Real.exp (-t))) (hz.trans_le hzb) hact hu hv hvalid
  have hcard := hB.card_le_available_of_density hG hz hρ hρq hdensity
  have hm := hardCoreAvailableMean_nonneg G S B hz.le
  have hc : A*(2*(z/(1+z))/ρ-1)≤Cs := by
    apply le_trans _ hCs
    apply mul_le_mul_of_nonneg_left _ hA
    gcongr
  apply hs.trans
  calc
    A*(B.card:ℝ)≤A*((2*(z/(1+z))/ρ-1)*hardCoreAvailableMean G S B z) :=
      mul_le_mul_of_nonneg_left hcard hA
    _ = (A*(2*(z/(1+z))/ρ-1))*hardCoreAvailableMean G S B z := by ring
    _ ≤ Cs*hardCoreAvailableMean G S B z := mul_le_mul_of_nonneg_right hc hm

theorem available_variance_bound {G : SimpleGraph V} {S B : Finset V}
    {z qa qb Cs D : ℝ} (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V))
    (hz : 0<z) (hqa : 0<qa) (hqaQ : qa≤z/(1+z)) (hQqb : z/(1+z)≤qb)
    (hCs : qb≤2*Cs) (hD : Cs/qa^2-(1-qa)/qa≤D)
    (hmarked : hardCoreMarkedVariance G S B z≤Cs*hardCoreAvailableMean G S B z) :
    hardCoreAvailableVariance G S B z≤D*hardCoreAvailableMean G S B z := by
  let q := z/(1+z)
  have hq : 0<q := by dsimp [q]; positivity
  have hm := hardCoreAvailableMean_nonneg G S B hz.le
  have heq := hardCoreMarkedVariance_eq_available_variance G S B hBS hB hz
  have hb : q^2*hardCoreAvailableVariance G S B z≤
      (Cs-q*(1-q))*hardCoreAvailableMean G S B z := by
    dsimp [q]
    nlinarith only [heq,hmarked]
  have hc : hardCoreAvailableVariance G S B z≤
      (Cs/q^2-(1-q)/q)*hardCoreAvailableMean G S B z := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hq)).mp
    calc
      q^2*hardCoreAvailableVariance G S B z≤_ := hb
      _ = q^2*((Cs/q^2-(1-q)/q)*hardCoreAvailableMean G S B z) := by field_simp
  have hcoef := (reciprocal_variance_coefficient_antitone hqa hqaQ (hQqb.trans hCs)).trans hD
  exact hc.trans (mul_le_mul_of_nonneg_right hcoef hm)

theorem centered_variance_bound {G : SimpleGraph V} {S B : Finset V}
    {z qb CW R : ℝ} (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V))
    (hz : 0<z) (hQqb : z/(1+z)≤qb) (hqb : qb<1) (hCW : 0≤CW)
    (hR : CW/(1-qb)-1≤R)
    (hselect : hardCoreVariance G S z≤CW*hardCoreOccupiedMass G S B z) :
    hardCoreLayerMeanVariance G S B z≤
      R*(z/(1+z)*(1-z/(1+z)))*hardCoreAvailableMean G S B z := by
  let q := z/(1+z)
  have hq : 0<q := by dsimp [q]; positivity
  have hm := hardCoreAvailableMean_nonneg G S B hz.le
  have heq := hardCoreVariance_eq_layer_variance G S B hBS hB hz
  have hmass := hardCoreOccupiedMass_eq_activity_available_mean G S B hBS hB hz
  rw [hmass] at hselect
  have hR1 : CW/(1-qb)≤R+1 := by linarith
  have hRp : 0≤R+1 := (div_nonneg hCW (by linarith)).trans hR1
  have hR2 : CW≤(R+1)*(1-qb) := (div_le_iff₀ (by linarith)).mp hR1
  have hR3 : CW≤(R+1)*(1-q) := hR2.trans
    (mul_le_mul_of_nonneg_left (by dsimp [q]; linarith) hRp)
  have hbound := mul_le_mul_of_nonneg_right hR3 (mul_nonneg hq.le hm)
  dsimp [q] at hbound
  nlinarith only [heq,hselect,hbound]


/-- All fields refer to the same original graph, activity, fixed maximizing
set, and actual available mean. -/
structure Bounds (G : SimpleGraph V) (S B : Finset V) (z : ℝ)
    (N : ℕ) (ρ qb Cs D R : ℝ) : Prop where
  mean_lower : ρ*N/(2*qb)≤hardCoreAvailableMean G S B z
  mean_pos : 0<hardCoreAvailableMean G S B z
  tilt_variance : ∀t≥0,
    heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
      (fun J=>((J∩B).card:ℝ))≤Cs*hardCoreAvailableMean G S B z
  available_variance : hardCoreAvailableVariance G S B z≤D*hardCoreAvailableMean G S B z
  centered_variance : hardCoreLayerMeanVariance G S B z≤
    R*(z/(1+z)*(1-z/(1+z)))*hardCoreAvailableMean G S B z

/-- Certified scalar sources, not assumed statistical bounds, imply the
whole mean-matched interface. The density input may come from a central-rank
condition or any genuine density theorem at this same activity. -/
theorem of_certificates {G : SimpleGraph V} {S B : Finset V}
    {z lower b bSource ρ qa qb A u v Cs D CW R : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (N : ℕ) (hN0 : 0<N) (hN : N≤S.card)
    (hlower : 0<lower) (hlo : lower≤z) (hhi : z≤b) (hsourceHi : z≤bSource)
    (hρ : 0<ρ) (hqa : 0<qa) (hqaQ : qa≤z/(1+z)) (hQqb : z/(1+z)≤qb) (hqb : qb<1)
    (hdensity : ρ*(S.card:ℝ)≤hardCoreMean G S z)
    (hA : 0≤A) (hu : 0≤u) (hv : 0≤v) (hnonnegative : NonnegativeSourceRowValid bSource A u v)
    (P : SelectionSourceParameters) (hP : P.Admissible) (hCJ : 0≤P.CJ) (hCmu : 0≤P.Cmu)
    (hselection : SelectionSourceRowValid P lower b) (hCW : P.CJ+2*P.Cmu≤CW)
    (hCs : A*(2*qb/ρ-1)≤Cs) (hCsq : qb≤2*Cs)
    (hD : Cs/qa^2-(1-qa)/qa≤D) (hR : CW/(1-qb)-1≤R) :
    Bounds G S B z N ρ qb Cs D R := by
  have hz : 0<z := hlower.trans_le hlo
  have hS : 0<S.card := hN0.trans_le hN
  have hρq := density_le_probability_cap G S hz hS hdensity
  have ht := tilt_variance_of_density hB hG hz hsourceHi hρ hρq hQqb hA hu hv hnonnegative hdensity hCs
  have hmarked : hardCoreMarkedVariance G S B z≤Cs*hardCoreAvailableMean G S B z := by
    have hzero := ht 0 le_rfl
    have hact0 : independentTiltActivities B z (Real.exp (-0))=(fun _=>z) := by
      funext x
      simp [independentTiltActivities]
    rw [hact0] at hzero
    exact hzero
  have hsource := hB.variance_le_mass_of_selection_certificate hG hlower hlo hhi P hP hCJ hCmu hselection
  have hm0 := hardCoreAvailableMean_nonneg G S B hz.le
  have hmass0 : 0≤hardCoreOccupiedMass G S B z := by
    rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz]
    exact mul_nonneg (by positivity) hm0
  have hselect : hardCoreVariance G S z≤CW*hardCoreOccupiedMass G S B z :=
    hsource.trans (mul_le_mul_of_nonneg_right hCW hmass0)
  have hCW0 : 0≤CW := (by positivity : 0≤P.CJ+2*P.Cmu).trans hCW
  have hmin := available_mean_lower hB hG hz hρ hQqb N hN hdensity
  have hNp : 0<(N:ℝ) := by exact_mod_cast hN0
  have hqb0 : 0<qb := (by positivity : 0<z/(1+z)).trans_le hQqb
  refine ⟨hmin,?_,ht,available_variance_bound hB.subset hB.independent hz hqa hqaQ hQqb
    hCsq hD hmarked,centered_variance_bound hB.subset hB.independent hz hQqb hqb hCW0 hR hselect⟩
  exact (by positivity : 0<ρ*N/(2*qb)).trans_le hmin

/-- At a chosen mean k, the squared offset in the Gaussian budget is exactly
the centered layer-mean variance already controlled by Bounds. -/
theorem Bounds.centered_sq_bound {G : SimpleGraph V} {S B : Finset V}
    {z ρ qb Cs D R k : ℝ} {N : ℕ} (h : Bounds G S B z N ρ qb Cs D R)
    (hIS : B⊆S) (hB : G.IsIndepSet (B:Set V)) (hz : 0<z)
    (hmean : hardCoreMean G S z=k) :
    hardCoreLayerExpectation G S B z (fun j d=>(k-binomialLayerMean j d z)^2)≤
      R*(z/(1+z)*(1-z/(1+z)))*hardCoreAvailableMean G S B z := by
  have he := hardCoreLayerExpectation_centered_sq G S B hIS hB hz hmean
  rw [hardCoreVariance_eq_layer_variance G S B hIS hB hz] at he
  have he' : hardCoreLayerExpectation G S B z (fun j d=>(k-binomialLayerMean j d z)^2)=
      hardCoreLayerMeanVariance G S B z := by linarith only [he]
  rw [he']
  exact h.centered_variance

#print axioms reciprocal_variance_coefficient_antitone
#print axioms available_mean_lower
#print axioms tilt_variance_of_density
#print axioms available_variance_bound
#print axioms centered_variance_bound
#print axioms of_certificates
#print axioms Bounds.centered_sq_bound
end ForestUnimodality.MeanMatchedSourceBudget

