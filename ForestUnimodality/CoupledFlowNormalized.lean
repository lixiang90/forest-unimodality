import ForestUnimodality.CoupledFlowTable

namespace ForestUnimodality.CoupledFlow
open Set
variable {V : Type*} [DecidableEq V]

theorem Table.actual_laplace_normalized (T : Table) {qb rho : ℚ}
    (hnorm : 0<rho ∧ rho≤T.qa ∧ T.qa≤qb ∧ qb<1 ∧
      T.environment.a≤T.qa/(1-T.qa) ∧ qb/(1-qb)≤T.environment.b ∧
      2*qb/rho-1≤T.environment.beta ∧ 2*qb/rho≤T.environment.gamma)
    (hinit : 2*qb≤T.initialUpper)
    (hheader : T.headerCheck=true)
    (hrows : (List.range T.n).all (fun i=>(T.row i).check T.environment)=true)
    (hedges : (List.range T.n).all T.connectionCheck=true)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Icc (T.qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z T.retention≤
      Real.exp (-(T.rate:ℝ)*hardCoreAvailableMean G S B z) := by
  rcases hnorm with ⟨hr,hrqa,hqaqb,hqb,ha,hb,hbeta,hgamma⟩
  have hrR : (0:ℝ)<rho := by exact_mod_cast hr
  have hrq : (rho:ℝ)≤z/(1+z) := (by exact_mod_cast hrqa : (rho:ℝ)≤T.qa).trans hq.1
  have hqbR : (qb:ℝ)<1 := by exact_mod_cast hqb
  have hqaR : (T.qa:ℝ)<1 := (by exact_mod_cast hqaqb : (T.qa:ℝ)≤qb).trans_lt hqbR
  have hzqhi : z≤(qb:ℝ)/(1-(qb:ℝ)) := by
    apply (le_div_iff₀ (by linarith : (0:ℝ)<1-(qb:ℝ))).mpr
    have hh := (div_le_iff₀ (by positivity : (0:ℝ)<1+z)).mp hq.2
    nlinarith
  have hzqlo : (T.qa:ℝ)/(1-(T.qa:ℝ))≤z := by
    apply (div_le_iff₀ (by linarith : (0:ℝ)<1-(T.qa:ℝ))).mpr
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<1+z)).mp hq.1
    nlinarith
  have hzlo : (T.environment.a:ℝ)≤z := (by exact_mod_cast ha :
    (T.environment.a:ℝ)≤(T.qa:ℝ)/(1-(T.qa:ℝ))).trans hzqlo
  have hzhi : z≤(T.environment.b:ℝ) := hzqhi.trans (by exact_mod_cast hb)
  have hn := FixedIndependentTilt.initial_normalized_bounds hB hG hz hrR hrq hq hdensity
  dsimp only at hn
  have hbetaR : 2*(qb:ℝ)/(rho:ℝ)-1≤T.environment.beta := by exact_mod_cast hbeta
  have hgammaR : 2*(qb:ℝ)/(rho:ℝ)≤T.environment.gamma := by exact_mod_cast hgamma
  have hBcard : (B.card:ℝ)≤hardCoreAvailableMean G S B z*(T.environment.beta:ℝ) := by
    have hh := hn.2.2.2.1.trans (mul_le_mul_of_nonneg_right hbetaR hn.1)
    simpa only [mul_comm] using hh
  have hScard : (S.card:ℝ)≤hardCoreAvailableMean G S B z*(T.environment.gamma:ℝ) := by
    have hh := hn.2.2.1.trans (mul_le_mul_of_nonneg_right hgammaR hn.1)
    simpa only [mul_comm] using hh
  have hCcard : ((S\B).card:ℝ)≤hardCoreAvailableMean G S B z*(T.environment.beta:ℝ) := by
    have hh := hn.2.2.2.2.1.trans (mul_le_mul_of_nonneg_right hbetaR hn.1)
    simpa only [mul_comm] using hh
  have hinitial : hardCoreAvailableMean G S B z*(T.qa:ℝ)≤hardCoreOccupiedMass G S B z := by
    have hh := hn.2.2.2.2.2.1
    rw [FixedIndependentTilt.markedMean_zero] at hh
    simpa only [mul_comm] using hh
  have hmu : FixedIndependentTilt.totalMean G S B z 0≤
      hardCoreAvailableMean G S B z*(T.initialUpper:ℝ) := by
    have hi : 2*(qb:ℝ)≤T.initialUpper := by exact_mod_cast hinit
    have hh := hn.2.2.2.2.2.2
    nlinarith [mul_le_mul_of_nonneg_left hi hn.1]
  have hh := T.actual_laplace hheader hrows hedges G hG S B hB.subset hB.independent
    hzlo hzhi hn.1 rfl hBcard hScard hCcard hinitial hmu
  simpa only [neg_mul,mul_neg,mul_comm] using hh

#print axioms Table.actual_laplace_normalized
end ForestUnimodality.CoupledFlow
