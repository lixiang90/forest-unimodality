import ForestUnimodality.LogVarianceProfileCertificate
import ForestUnimodality.Stage80KernelData.Cell173.Budget
import ForestUnimodality.Stage80MessageSourceData.Case053.Parameters

/-! Concrete scalar profile and graph conversion. Source validity is an explicit
premise until the independently checked message source is supplied. -/
namespace ForestUnimodality.Stage80LogVarianceData.Cell173
open Stage80KernelData.Cell173
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def certificate : LogVarianceProfileCertificate.Certificate where
  qa := interval.lo
  qb := interval.hi
  a := interval.lo/(1-interval.lo)
  lower := Stage80MessageSourceData.Case053.parameters.lower
  b := Stage80MessageSourceData.Case053.parameters.upper
  C := Stage80MessageSourceData.Case053.parameters.CJ
  Cmu := Stage80MessageSourceData.Case053.parameters.Cmu
  D := Stage80MessageSourceData.Case053.parameters.Dn
  ell := Stage80MessageSourceData.Case053.parameters.ell
  alpha := alpha
  beta := varianceIntercept
  nlo := 80
  nhi := 98
  rankUpper := 24
  logNLo := (-87336799687546045860073747678279480079/10000000000000000000000000000000000000000)
  logNHi := (-43668399843773022930036873839139740037/5000000000000000000000000000000000000000)
  logRootLo := (4238142467763609170377481944299123939011/10000000000000000000000000000000000000000)
  logRootHi := (529767808470451146297185243037390492377/1250000000000000000000000000000000000000)
  logN := ⟨⟨1, (-87336799687546045860073747678279480079/10000000000000000000000000000000000000000), 64, (99130434782608695652173913043478260869536639636049/100000000000000000000000000000000000000000000000000), (1982608695652173913043478260869565217390732792721/2000000000000000000000000000000000000000000000000)⟩, ⟨1, (-43668399843773022930036873839139740037/5000000000000000000000000000000000000000), 64, (99130434782608695652173913043478260869586204853441/100000000000000000000000000000000000000000000000000), (49565217391304347826086956521739130434793102426721/50000000000000000000000000000000000000000000000000)⟩, (99130434782608695652173913043478260869536639636049/100000000000000000000000000000000000000000000000000), (1982608695652173913043478260869565217390732792721/2000000000000000000000000000000000000000000000000), (99130434782608695652173913043478260869586204853441/100000000000000000000000000000000000000000000000000), (49565217391304347826086956521739130434793102426721/50000000000000000000000000000000000000000000000000)⟩
  logRoot := ⟨⟨1, (4238142467763609170377481944299123939011/10000000000000000000000000000000000000000), 64, (76388888888888888888888888888888888888871562067783/50000000000000000000000000000000000000000000000000), (152777777777777777777777777777777777777743124135567/100000000000000000000000000000000000000000000000000)⟩, ⟨1, (529767808470451146297185243037390492377/1250000000000000000000000000000000000000), 64, (30555555555555555555555555555555555555563902604891/20000000000000000000000000000000000000000000000000), (19097222222222222222222222222222222222227439128057/12500000000000000000000000000000000000000000000000)⟩, (76388888888888888888888888888888888888871562067783/50000000000000000000000000000000000000000000000000), (152777777777777777777777777777777777777743124135567/100000000000000000000000000000000000000000000000000), (30555555555555555555555555555555555555563902604891/20000000000000000000000000000000000000000000000000), (19097222222222222222222222222222222222227439128057/12500000000000000000000000000000000000000000000000)⟩

theorem checked : certificate.check=true := by decide +kernel

theorem activity_bounds {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    (certificate.a:ℝ)≤z ∧ z≤(Stage80MessageSourceData.Case053.parameters.upper:ℝ) := by
  have hl := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  have hu := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
  norm_num [certificate,interval,Stage80MessageSourceData.Case053.parameters,Stage80MessagePriceData.case053] at hl hu ⊢
  constructor <;> linarith

theorem actual_variance_of_source_valid
    (hsource : MessageSourceRowValid Stage80MessageSourceData.Case053.parameters.toReal
      Stage80MessageSourceData.Case053.parameters.lower Stage80MessageSourceData.Case053.parameters.upper)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 80≤S.card) (hN : S.card≤98) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hmean : hardCoreMean G S z=k)
    (hm : hardCoreAvailableMean G S B z≤(mhi:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept := by
  have hab := activity_bounds hz hq
  have hp := MessagePriceSpline.Parameters.check_sound Stage80MessageSourceData.Case053.parameters_checked
  have hlo : Stage80MessageSourceData.Case053.parameters.toReal.w=0 ∨ (Stage80MessageSourceData.Case053.parameters.lower:ℝ)≤z := by
    left
    norm_num [Stage80MessageSourceData.Case053.parameters,Stage80MessagePriceData.case053,MessagePriceSpline.Parameters.toReal]
  have hv := hB.variance_le_mass_and_mean_with_log_bonus hG
    (Finset.card_pos.mp (by omega)) hp.1 hz hab.2 Stage80MessageSourceData.Case053.parameters.toReal hp.2.2.2.2 hp.2.2.1 hlo hsource
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz,hmean] at hv
  have hk : k≤24 := integer_rank_upper_of_available_mean hB hG hz
    (by norm_num [interval]) hq.2 hm hmean (by norm_num [interval,mhi])
  exact certificate.check_sound checked hab.1 (by positivity)
    (by norm_num [certificate]; exact_mod_cast hn) (by norm_num [certificate]; exact_mod_cast hN)
    (hardCoreAvailableMean_nonneg G S B hz.le)
    (by norm_num [certificate]; exact_mod_cast hk) hq hv

#print axioms checked
#print axioms activity_bounds
#print axioms actual_variance_of_source_valid
end ForestUnimodality.Stage80LogVarianceData.Cell173
