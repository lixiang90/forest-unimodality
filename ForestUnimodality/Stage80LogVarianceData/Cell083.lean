import ForestUnimodality.LogVarianceProfileCertificate
import ForestUnimodality.Stage80KernelData.Cell083.Budget
import ForestUnimodality.Stage80MessageSourceData.Case059.Parameters

/-! Concrete scalar profile and graph conversion. Source validity is an explicit
premise until the independently checked message source is supplied. -/
namespace ForestUnimodality.Stage80LogVarianceData.Cell083
open Stage80KernelData.Cell083
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def certificate : LogVarianceProfileCertificate.Certificate where
  qa := interval.lo
  qb := interval.hi
  a := interval.lo/(1-interval.lo)
  lower := Stage80MessageSourceData.Case059.parameters.lower
  b := Stage80MessageSourceData.Case059.parameters.upper
  C := Stage80MessageSourceData.Case059.parameters.CJ
  Cmu := Stage80MessageSourceData.Case059.parameters.Cmu
  D := Stage80MessageSourceData.Case059.parameters.Dn
  ell := Stage80MessageSourceData.Case059.parameters.ell
  alpha := alpha
  beta := varianceIntercept
  nlo := 80
  nhi := 98
  rankUpper := 23
  logNLo := (49998200674328968738217020892869843021/10000000000000000000000000000000000000000)
  logNHi := (24999100337164484369108510446434921513/5000000000000000000000000000000000000000)
  logRootLo := (4037844354436461085493712537642833423129/10000000000000000000000000000000000000000)
  logRootHi := (2018922177218230542746856268821416711567/5000000000000000000000000000000000000000)
  logN := ⟨⟨1, (49998200674328968738217020892869843021/10000000000000000000000000000000000000000), 64, (12562654250311681042159631580286492125279667426153/12500000000000000000000000000000000000000000000000), (4020049360099737933491082105691677480089493576369/4000000000000000000000000000000000000000000000000)⟩, ⟨1, (24999100337164484369108510446434921513/5000000000000000000000000000000000000000), 64, (50250617001246724168638526321145968501143795013113/50000000000000000000000000000000000000000000000000), (100501234002493448337277052642291937002287590026227/100000000000000000000000000000000000000000000000000)⟩, (12562654250311681042159631580286492125279667426153/12500000000000000000000000000000000000000000000000), (4020049360099737933491082105691677480089493576369/4000000000000000000000000000000000000000000000000), (50250617001246724168638526321145968501143795013113/50000000000000000000000000000000000000000000000000), (100501234002493448337277052642291937002287590026227/100000000000000000000000000000000000000000000000000)⟩
  logRoot := ⟨⟨1, (4037844354436461085493712537642833423129/10000000000000000000000000000000000000000), 64, (149748110831234256926952141057934508816085641444909/100000000000000000000000000000000000000000000000000), (14974811083123425692695214105793450881608564144491/10000000000000000000000000000000000000000000000000)⟩, ⟨1, (2018922177218230542746856268821416711567/5000000000000000000000000000000000000000), 64, (5989924433249370277078085642317380352646420620013/4000000000000000000000000000000000000000000000000), (74874055415617128463476070528967254408080257750163/50000000000000000000000000000000000000000000000000)⟩, (149748110831234256926952141057934508816085641444909/100000000000000000000000000000000000000000000000000), (14974811083123425692695214105793450881608564144491/10000000000000000000000000000000000000000000000000), (5989924433249370277078085642317380352646420620013/4000000000000000000000000000000000000000000000000), (74874055415617128463476070528967254408080257750163/50000000000000000000000000000000000000000000000000)⟩

theorem checked : certificate.check=true := by decide +kernel

theorem activity_bounds {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    (certificate.a:ℝ)≤z ∧ z≤(Stage80MessageSourceData.Case059.parameters.upper:ℝ) := by
  have hl := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  have hu := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
  norm_num [certificate,interval,Stage80MessageSourceData.Case059.parameters,Stage80MessagePriceData.case059] at hl hu ⊢
  constructor <;> linarith

theorem actual_variance_of_source_valid
    (hsource : MessageSourceRowValid Stage80MessageSourceData.Case059.parameters.toReal
      Stage80MessageSourceData.Case059.parameters.lower Stage80MessageSourceData.Case059.parameters.upper)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 80≤S.card) (hN : S.card≤98) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hmean : hardCoreMean G S z=k)
    (hm : hardCoreAvailableMean G S B z≤(mhi:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept := by
  have hab := activity_bounds hz hq
  have hp := MessagePriceSpline.Parameters.check_sound Stage80MessageSourceData.Case059.parameters_checked
  have hlo : Stage80MessageSourceData.Case059.parameters.toReal.w=0 ∨ (Stage80MessageSourceData.Case059.parameters.lower:ℝ)≤z := by
    left
    norm_num [Stage80MessageSourceData.Case059.parameters,Stage80MessagePriceData.case059,MessagePriceSpline.Parameters.toReal]
  have hv := hB.variance_le_mass_and_mean_with_log_bonus hG
    (Finset.card_pos.mp (by omega)) hp.1 hz hab.2 Stage80MessageSourceData.Case059.parameters.toReal hp.2.2.2.2 hp.2.2.1 hlo hsource
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
end ForestUnimodality.Stage80LogVarianceData.Cell083
