import ForestUnimodality.BasicFlowTable
import ForestUnimodality.FlowNormalization

namespace ForestUnimodality.BasicFlow
open Set
variable {V : Type*} [DecidableEq V]

theorem Table.actual_laplace_normalized (T : Table) {qb rho : ℚ}
    (hnorm : 0<rho ∧ rho≤T.qa ∧ T.qa≤qb ∧ qb<1 ∧
      qb/(1-qb)≤T.b ∧ 2*qb/rho-1≤T.beta)
    (hheader : T.headerCheck=true)
    (hrows : (List.range T.n).all (fun i=>(T.row i).check T.b T.beta)=true)
    (hedges : (List.range T.n).all T.connectionCheck=true)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Icc (T.qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z T.retention≤
      Real.exp (-(T.rate:ℝ)*hardCoreAvailableMean G S B z) := by
  rcases hnorm with ⟨hr,hrqa,_,hqb,hb,hbeta⟩
  have hrR : (0:ℝ)<rho := by exact_mod_cast hr
  have hrq : (rho:ℝ)≤z/(1+z) := (by exact_mod_cast hrqa : (rho:ℝ)≤T.qa).trans hq.1
  have hqbR : (qb:ℝ)<1 := by exact_mod_cast hqb
  have hzq : z≤(qb:ℝ)/(1-(qb:ℝ)) := by
    apply (le_div_iff₀ (by linarith : (0:ℝ)<1-(qb:ℝ))).mpr
    have hh := (div_le_iff₀ (by positivity : (0:ℝ)<1+z)).mp hq.2
    nlinarith
  have hzb : z≤(T.b:ℝ) := hzq.trans (by exact_mod_cast hb)
  have hn := FixedIndependentTilt.initial_normalized_bounds hB hG hz hrR hrq hq hdensity
  dsimp only at hn
  have hbetaR : 2*(qb:ℝ)/(rho:ℝ)-1≤T.beta := by exact_mod_cast hbeta
  have hcard : (B.card:ℝ)≤hardCoreAvailableMean G S B z*(T.beta:ℝ) := by
    have hh := hn.2.2.2.1.trans (mul_le_mul_of_nonneg_right hbetaR hn.1)
    simpa only [mul_comm] using hh
  have hinitial : hardCoreAvailableMean G S B z*(T.qa:ℝ)≤hardCoreOccupiedMass G S B z := by
    have hh := hn.2.2.2.2.2.1
    rw [FixedIndependentTilt.markedMean_zero] at hh
    simpa only [mul_comm] using hh
  have hh := T.actual_laplace hheader hrows hedges G hG S B hB.subset hB.independent
    hz hzb hn.1 hcard hinitial
  simpa only [neg_mul,mul_neg,mul_comm] using hh

#print axioms Table.actual_laplace_normalized
end ForestUnimodality.BasicFlow
