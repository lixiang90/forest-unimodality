import ForestUnimodality.MessageLogBonus
import ForestUnimodality.LogVarianceProfile
import ForestUnimodality.MarginalIndependent
import ForestUnimodality.LaplaceRateInterval

/-! Keep the actual integer mean in a logarithmic variance bound. The source
certificate, size interval, and integer upper bound remain explicit premises. -/
namespace ForestUnimodality
variable {V : Type*} [DecidableEq V]

theorem IsMaximumMarginalIndependentOn.variance_le_mass_and_mean_with_log_bonus
    {G : SimpleGraph V} {S I : Finset V} {lower b z : ℝ}
    (hI : IsMaximumMarginalIndependentOn G S I z) (hG : G.IsAcyclic)
    (hS : S.Nonempty) (hlower : 0<lower) (hz : 0<z) (hhi : z≤b)
    (P : MessageSourceParameters) (hP : P.Admissible b) (hCJ : 0≤P.CJ)
    (hlo : P.w=0 ∨ lower≤z) (hvalid : MessageSourceRowValid P lower b) :
    hardCoreVariance G S z≤
      P.CJ*hardCoreOccupiedMass G S I z+P.Cmu*hardCoreMean G S z+
      (P.Dn-P.ell*Real.log (z/lower))*(S.card:ℝ)-
      P.ell*Real.log (1+z/(1+b)) := by
  have hv := forest_message_variance_with_log_bonus G hG S hS
    hlower hz hhi P hP hlo hvalid
  have hs := mul_le_mul_of_nonneg_left (hI.forest_selection_bound hG hz hhi) hCJ
  linarith

theorem integer_rank_upper_of_available_mean
    {G : SimpleGraph V} {S B : Finset V} {z qb mhi : ℝ} {k K : ℕ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hqb : 0≤qb) (hq : z/(1+z)≤qb)
    (hm : hardCoreAvailableMean G S B z≤mhi)
    (hmean : hardCoreMean G S z=k) (hstrict : 2*qb*mhi<(K:ℝ)+1) : k≤K := by
  have hhalf := hB.half_mean hG.isBipartite
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz,
    hmean] at hhalf
  have hprod : z/(1+z)*hardCoreAvailableMean G S B z≤qb*mhi :=
    (mul_le_mul_of_nonneg_right hq (hardCoreAvailableMean_nonneg G S B hz.le)).trans
      (mul_le_mul_of_nonneg_left hm hqb)
  have hkR : (k:ℝ)<(K:ℝ)+1 := by linarith
  have hkN : k<K+1 := by exact_mod_cast hkR
  omega

theorem log_variance_profile_of_rank_bound
    {C Cmu D ell a b lower qa qb q alpha beta g root logn logroot
      z nlo nhi n m variance k K : ℝ}
    (ha : 0<a) (hlower : 0<lower) (hb : 0<1+b) (haz : a≤z)
    (hell : 0≤ell) (hn : 0≤n) (hnlo : nlo≤n) (hnhi : n≤nhi) (hm : 0≤m)
    (hCmu : 0≤Cmu) (hk : k≤K) (hq : q∈Set.Icc qa qb)
    (hslo : C*qa-qa*(1-qa)≤alpha) (hshi : C*qb-qb*(1-qb)≤alpha)
    (hlogn : logn≤Real.log (a/lower))
    (hlogroot : logroot≤Real.log (1+a/(1+b)))
    (hg : D-ell*logn≤g) (hroot : root≤ell*logroot)
    (hbetalo : g*nlo-root+Cmu*K≤beta) (hbetahi : g*nhi-root+Cmu*K≤beta)
    (hvariance : variance≤C*(q*m)+Cmu*k+(D-ell*Real.log (z/lower))*n-
      ell*Real.log (1+z/(1+b))) :
    variance≤(q*(1-q)+alpha)*m+beta := by
  have hrank := mul_le_mul_of_nonneg_left hk hCmu
  have hv : variance-Cmu*K≤C*(q*m)+(D-ell*Real.log (z/lower))*n-
      ell*Real.log (1+z/(1+b)) := by linarith
  have h := log_variance_profile (beta:=beta-Cmu*K) ha hlower hb haz hell hn hnlo hnhi hm
    hq hslo hshi hlogn hlogroot hg hroot (by linarith) (by linarith) hv
  linarith

#print axioms IsMaximumMarginalIndependentOn.variance_le_mass_and_mean_with_log_bonus
#print axioms integer_rank_upper_of_available_mean
#print axioms log_variance_profile_of_rank_bound
end ForestUnimodality
