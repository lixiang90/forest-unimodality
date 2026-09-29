import ForestUnimodality.LogVarianceProfileCertificate
import ForestUnimodality.Stage80KernelData.Cell071.Budget
import ForestUnimodality.Stage80MessageSourceData.Case057.Parameters

/-! Concrete scalar profile and graph conversion. Source validity is an explicit
premise until the independently checked message source is supplied. -/
namespace ForestUnimodality.Stage80LogVarianceData.Cell071
open Stage80KernelData.Cell071
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def certificate : LogVarianceProfileCertificate.Certificate where
  qa := interval.lo
  qb := interval.hi
  a := interval.lo/(1-interval.lo)
  lower := Stage80MessageSourceData.Case057.parameters.lower
  b := Stage80MessageSourceData.Case057.parameters.upper
  C := Stage80MessageSourceData.Case057.parameters.CJ
  Cmu := Stage80MessageSourceData.Case057.parameters.Cmu
  D := Stage80MessageSourceData.Case057.parameters.Dn
  ell := Stage80MessageSourceData.Case057.parameters.ell
  alpha := alpha
  beta := varianceIntercept
  nlo := 80
  nhi := 98
  rankUpper := 23
  logNLo := (25776135760069297323585030266030231313/2500000000000000000000000000000000000000)
  logNHi := (103104543040277189294340121064120925257/10000000000000000000000000000000000000000)
  logRootLo := (996727795589434072812734623908741036031/2500000000000000000000000000000000000000)
  logRootHi := (3986911182357736291250938495634964144129/10000000000000000000000000000000000000000)
  logN := ⟨⟨1, (25776135760069297323585030266030231313/2500000000000000000000000000000000000000), 64, (2020727580372250423011844331641285956006255419109/2000000000000000000000000000000000000000000000000), (101036379018612521150592216582064297800312770955451/100000000000000000000000000000000000000000000000000)⟩, ⟨1, (103104543040277189294340121064120925257/10000000000000000000000000000000000000000), 64, (101036379018612521150592216582064297800363289144959/100000000000000000000000000000000000000000000000000), (157869342216582064297800338409475465313067639289/156250000000000000000000000000000000000000000000)⟩, (2020727580372250423011844331641285956006255419109/2000000000000000000000000000000000000000000000000), (101036379018612521150592216582064297800312770955451/100000000000000000000000000000000000000000000000000), (101036379018612521150592216582064297800363289144959/100000000000000000000000000000000000000000000000000), (157869342216582064297800338409475465313067639289/156250000000000000000000000000000000000000000000)⟩
  logRoot := ⟨⟨1, (996727795589434072812734623908741036031/2500000000000000000000000000000000000000), 64, (148987335281751525406347741373122083781942227322289/100000000000000000000000000000000000000000000000000), (14898733528175152540634774137312208378194222732229/10000000000000000000000000000000000000000000000000)⟩, ⟨1, (3986911182357736291250938495634964144129/10000000000000000000000000000000000000000), 64, (14898733528175152540634774137312208378201672098993/10000000000000000000000000000000000000000000000000), (148987335281751525406347741373122083782016720989931/100000000000000000000000000000000000000000000000000)⟩, (148987335281751525406347741373122083781942227322289/100000000000000000000000000000000000000000000000000), (14898733528175152540634774137312208378194222732229/10000000000000000000000000000000000000000000000000), (14898733528175152540634774137312208378201672098993/10000000000000000000000000000000000000000000000000), (148987335281751525406347741373122083782016720989931/100000000000000000000000000000000000000000000000000)⟩

theorem checked : certificate.check=true := by decide +kernel

theorem activity_bounds {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    (certificate.a:ℝ)≤z ∧ z≤(Stage80MessageSourceData.Case057.parameters.upper:ℝ) := by
  have hl := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  have hu := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
  norm_num [certificate,interval,Stage80MessageSourceData.Case057.parameters,Stage80MessagePriceData.case057] at hl hu ⊢
  constructor <;> linarith

theorem actual_variance_of_source_valid
    (hsource : MessageSourceRowValid Stage80MessageSourceData.Case057.parameters.toReal
      Stage80MessageSourceData.Case057.parameters.lower Stage80MessageSourceData.Case057.parameters.upper)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 80≤S.card) (hN : S.card≤98) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hmean : hardCoreMean G S z=k)
    (hm : hardCoreAvailableMean G S B z≤(mhi:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept := by
  have hab := activity_bounds hz hq
  have hp := MessagePriceSpline.Parameters.check_sound Stage80MessageSourceData.Case057.parameters_checked
  have hlo : Stage80MessageSourceData.Case057.parameters.toReal.w=0 ∨ (Stage80MessageSourceData.Case057.parameters.lower:ℝ)≤z := by
    right
    norm_num [certificate,Stage80MessageSourceData.Case057.parameters,Stage80MessagePriceData.case057,interval] at hab ⊢; linarith
  have hv := hB.variance_le_mass_and_mean_with_log_bonus hG
    (Finset.card_pos.mp (by omega)) hp.1 hz hab.2 Stage80MessageSourceData.Case057.parameters.toReal hp.2.2.2.2 hp.2.2.1 hlo hsource
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz,hmean] at hv
  have hk : k≤23 := integer_rank_upper_of_available_mean hB hG hz
    (by norm_num [interval]) hq.2 hm hmean (by norm_num [interval,mhi])
  exact certificate.check_sound checked hab.1 (by positivity)
    (by norm_num [certificate]; exact_mod_cast hn) (by norm_num [certificate]; exact_mod_cast hN)
    (hardCoreAvailableMean_nonneg G S B hz.le)
    (by norm_num [certificate]; exact_mod_cast hk) hq hv

#print axioms checked
#print axioms activity_bounds
#print axioms actual_variance_of_source_valid
end ForestUnimodality.Stage80LogVarianceData.Cell071
