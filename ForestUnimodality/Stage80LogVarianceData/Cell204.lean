import ForestUnimodality.LogVarianceProfileCertificate
import ForestUnimodality.Stage80KernelData.Cell204.Budget
import ForestUnimodality.Stage80MessageSourceData.Case061.Parameters

/-! Concrete scalar profile and graph conversion. Source validity is an explicit
premise until the independently checked message source is supplied. -/
namespace ForestUnimodality.Stage80LogVarianceData.Cell204
open Stage80KernelData.Cell204
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def certificate : LogVarianceProfileCertificate.Certificate where
  qa := interval.lo
  qb := interval.hi
  a := interval.lo/(1-interval.lo)
  lower := Stage80MessageSourceData.Case061.parameters.lower
  b := Stage80MessageSourceData.Case061.parameters.upper
  C := Stage80MessageSourceData.Case061.parameters.CJ
  Cmu := Stage80MessageSourceData.Case061.parameters.Cmu
  D := Stage80MessageSourceData.Case061.parameters.Dn
  ell := Stage80MessageSourceData.Case061.parameters.ell
  alpha := alpha
  beta := varianceIntercept
  nlo := 80
  nhi := 98
  rankUpper := 26
  logNLo := (-5007737835217879605041361009561422573/312500000000000000000000000000000000000)
  logNHi := (-160247610726972147361323552305965522331/10000000000000000000000000000000000000000)
  logRootLo := (555167811584148080574527255154020412403/1250000000000000000000000000000000000000)
  logRootHi := (4441342492673184644596218041232163299229/10000000000000000000000000000000000000000)
  logN := ⟨⟨1, (-5007737835217879605041361009561422573/312500000000000000000000000000000000000), 64, (98410295230885692657077971233913701741080495064031/100000000000000000000000000000000000000000000000000), (3075321725965177895533686601059803179408765470751/3125000000000000000000000000000000000000000000000)⟩, ⟨1, (-160247610726972147361323552305965522331/10000000000000000000000000000000000000000), 64, (49205147615442846328538985616956850870564850105823/50000000000000000000000000000000000000000000000000), (98410295230885692657077971233913701741129700211647/100000000000000000000000000000000000000000000000000)⟩, (98410295230885692657077971233913701741080495064031/100000000000000000000000000000000000000000000000000), (3075321725965177895533686601059803179408765470751/3125000000000000000000000000000000000000000000000), (49205147615442846328538985616956850870564850105823/50000000000000000000000000000000000000000000000000), (98410295230885692657077971233913701741129700211647/100000000000000000000000000000000000000000000000000)⟩
  logRoot := ⟨⟨1, (555167811584148080574527255154020412403/1250000000000000000000000000000000000000), 64, (155913978494623655913978494623655913978450222490593/100000000000000000000000000000000000000000000000000), (77956989247311827956989247311827956989225111245297/50000000000000000000000000000000000000000000000000)⟩, ⟨1, (4441342492673184644596218041232163299229/10000000000000000000000000000000000000000), 64, (974462365591397849462365591397849462365801121749/625000000000000000000000000000000000000000000000), (155913978494623655913978494623655913978528179479841/100000000000000000000000000000000000000000000000000)⟩, (155913978494623655913978494623655913978450222490593/100000000000000000000000000000000000000000000000000), (77956989247311827956989247311827956989225111245297/50000000000000000000000000000000000000000000000000), (974462365591397849462365591397849462365801121749/625000000000000000000000000000000000000000000000), (155913978494623655913978494623655913978528179479841/100000000000000000000000000000000000000000000000000)⟩

theorem checked : certificate.check=true := by decide +kernel

theorem activity_bounds {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    (certificate.a:ℝ)≤z ∧ z≤(Stage80MessageSourceData.Case061.parameters.upper:ℝ) := by
  have hl := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  have hu := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
  norm_num [certificate,interval,Stage80MessageSourceData.Case061.parameters,Stage80MessagePriceData.case061] at hl hu ⊢
  constructor <;> linarith

theorem actual_variance_of_source_valid
    (hsource : MessageSourceRowValid Stage80MessageSourceData.Case061.parameters.toReal
      Stage80MessageSourceData.Case061.parameters.lower Stage80MessageSourceData.Case061.parameters.upper)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 80≤S.card) (hN : S.card≤98) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hmean : hardCoreMean G S z=k)
    (hm : hardCoreAvailableMean G S B z≤(mhi:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept := by
  have hab := activity_bounds hz hq
  have hp := MessagePriceSpline.Parameters.check_sound Stage80MessageSourceData.Case061.parameters_checked
  have hlo : Stage80MessageSourceData.Case061.parameters.toReal.w=0 ∨ (Stage80MessageSourceData.Case061.parameters.lower:ℝ)≤z := by
    left
    norm_num [Stage80MessageSourceData.Case061.parameters,Stage80MessagePriceData.case061,MessagePriceSpline.Parameters.toReal]
  have hv := hB.variance_le_mass_and_mean_with_log_bonus hG
    (Finset.card_pos.mp (by omega)) hp.1 hz hab.2 Stage80MessageSourceData.Case061.parameters.toReal hp.2.2.2.2 hp.2.2.1 hlo hsource
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz,hmean] at hv
  have hk : k≤26 := integer_rank_upper_of_available_mean hB hG hz
    (by norm_num [interval]) hq.2 hm hmean (by norm_num [interval,mhi])
  exact certificate.check_sound checked hab.1 (by positivity)
    (by norm_num [certificate]; exact_mod_cast hn) (by norm_num [certificate]; exact_mod_cast hN)
    (hardCoreAvailableMean_nonneg G S B hz.le)
    (by norm_num [certificate]; exact_mod_cast hk) hq hv

#print axioms checked
#print axioms activity_bounds
#print axioms actual_variance_of_source_valid
end ForestUnimodality.Stage80LogVarianceData.Cell204
