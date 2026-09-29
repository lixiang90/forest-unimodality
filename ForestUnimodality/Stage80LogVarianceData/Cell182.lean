import ForestUnimodality.LogVarianceProfileCertificate
import ForestUnimodality.Stage80KernelData.Cell182.Budget
import ForestUnimodality.Stage80MessageSourceData.Case054.Parameters

/-! Concrete scalar profile and graph conversion. Source validity is an explicit
premise until the independently checked message source is supplied. -/
namespace ForestUnimodality.Stage80LogVarianceData.Cell182
open Stage80KernelData.Cell182
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def certificate : LogVarianceProfileCertificate.Certificate where
  qa := interval.lo
  qb := interval.hi
  a := interval.lo/(1-interval.lo)
  lower := Stage80MessageSourceData.Case054.parameters.lower
  b := Stage80MessageSourceData.Case054.parameters.upper
  C := Stage80MessageSourceData.Case054.parameters.CJ
  Cmu := Stage80MessageSourceData.Case054.parameters.Cmu
  D := Stage80MessageSourceData.Case054.parameters.Dn
  ell := Stage80MessageSourceData.Case054.parameters.ell
  alpha := alpha
  beta := varianceIntercept
  nlo := 80
  nhi := 98
  rankUpper := 24
  logNLo := (-2175549513874928012273277036460922833/500000000000000000000000000000000000000)
  logNHi := (-8702198055499712049093108145843691331/2000000000000000000000000000000000000000)
  logRootLo := (2140589909603562373324135419469629057061/5000000000000000000000000000000000000000)
  logRootHi := (4281179819207124746648270838939258114127/10000000000000000000000000000000000000000)
  logN := ⟨⟨1, (-2175549513874928012273277036460922833/500000000000000000000000000000000000000), 64, (995658353289332788193836029826918209605922088199/1000000000000000000000000000000000000000000000000), (99565835328933278819383602982691820960592208819901/100000000000000000000000000000000000000000000000000)⟩, ⟨1, (-8702198055499712049093108145843691331/2000000000000000000000000000000000000000), 64, (19913167065786655763876720596538364192128398347513/20000000000000000000000000000000000000000000000000), (49782917664466639409691801491345910480320995868783/50000000000000000000000000000000000000000000000000)⟩, (995658353289332788193836029826918209605922088199/1000000000000000000000000000000000000000000000000), (99565835328933278819383602982691820960592208819901/100000000000000000000000000000000000000000000000000), (19913167065786655763876720596538364192128398347513/20000000000000000000000000000000000000000000000000), (49782917664466639409691801491345910480320995868783/50000000000000000000000000000000000000000000000000)⟩
  logRoot := ⟨⟨1, (2140589909603562373324135419469629057061/5000000000000000000000000000000000000000), 64, (15343670978662932854067835572924285803846274525279/10000000000000000000000000000000000000000000000000), (153436709786629328540678355729242858038462745252791/100000000000000000000000000000000000000000000000000)⟩, ⟨1, (4281179819207124746648270838939258114127/10000000000000000000000000000000000000000), 64, (38359177446657332135169588932310714509634865901921/25000000000000000000000000000000000000000000000000), (30687341957325865708135671145848571607707892721537/20000000000000000000000000000000000000000000000000)⟩, (15343670978662932854067835572924285803846274525279/10000000000000000000000000000000000000000000000000), (153436709786629328540678355729242858038462745252791/100000000000000000000000000000000000000000000000000), (38359177446657332135169588932310714509634865901921/25000000000000000000000000000000000000000000000000), (30687341957325865708135671145848571607707892721537/20000000000000000000000000000000000000000000000000)⟩

theorem checked : certificate.check=true := by decide +kernel

theorem activity_bounds {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    (certificate.a:ℝ)≤z ∧ z≤(Stage80MessageSourceData.Case054.parameters.upper:ℝ) := by
  have hl := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  have hu := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
  norm_num [certificate,interval,Stage80MessageSourceData.Case054.parameters,Stage80MessagePriceData.case054] at hl hu ⊢
  constructor <;> linarith

theorem actual_variance_of_source_valid
    (hsource : MessageSourceRowValid Stage80MessageSourceData.Case054.parameters.toReal
      Stage80MessageSourceData.Case054.parameters.lower Stage80MessageSourceData.Case054.parameters.upper)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 80≤S.card) (hN : S.card≤98) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hmean : hardCoreMean G S z=k)
    (hm : hardCoreAvailableMean G S B z≤(mhi:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept := by
  have hab := activity_bounds hz hq
  have hp := MessagePriceSpline.Parameters.check_sound Stage80MessageSourceData.Case054.parameters_checked
  have hlo : Stage80MessageSourceData.Case054.parameters.toReal.w=0 ∨ (Stage80MessageSourceData.Case054.parameters.lower:ℝ)≤z := by
    left
    norm_num [Stage80MessageSourceData.Case054.parameters,Stage80MessagePriceData.case054,MessagePriceSpline.Parameters.toReal]
  have hv := hB.variance_le_mass_and_mean_with_log_bonus hG
    (Finset.card_pos.mp (by omega)) hp.1 hz hab.2 Stage80MessageSourceData.Case054.parameters.toReal hp.2.2.2.2 hp.2.2.1 hlo hsource
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
end ForestUnimodality.Stage80LogVarianceData.Cell182
