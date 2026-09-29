import ForestUnimodality.LogVarianceProfileCertificate
import ForestUnimodality.Stage80KernelData.Cell059.Budget
import ForestUnimodality.Stage80MessageSourceData.Case056.Parameters

/-! Concrete scalar profile and graph conversion. Source validity is an explicit
premise until the independently checked message source is supplied. -/
namespace ForestUnimodality.Stage80LogVarianceData.Cell059
open Stage80KernelData.Cell059
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def certificate : LogVarianceProfileCertificate.Certificate where
  qa := interval.lo
  qb := interval.hi
  a := interval.lo/(1-interval.lo)
  lower := Stage80MessageSourceData.Case056.parameters.lower
  b := Stage80MessageSourceData.Case056.parameters.upper
  C := Stage80MessageSourceData.Case056.parameters.CJ
  Cmu := Stage80MessageSourceData.Case056.parameters.Cmu
  D := Stage80MessageSourceData.Case056.parameters.Dn
  ell := Stage80MessageSourceData.Case056.parameters.ell
  alpha := alpha
  beta := varianceIntercept
  nlo := 80
  nhi := 98
  rankUpper := 23
  logNLo := (105281267668918821974492463341976835441/10000000000000000000000000000000000000000)
  logNHi := (52640633834459410987246231670988417723/5000000000000000000000000000000000000000)
  logRootLo := (79038197017531729591459676867236843477/200000000000000000000000000000000000000)
  logRootHi := (790381970175317295914596768672368434771/2000000000000000000000000000000000000000)
  logN := ⟨⟨1, (105281267668918821974492463341976835441/10000000000000000000000000000000000000000), 64, (50529187124931805782869612656846699399878828370143/50000000000000000000000000000000000000000000000000), (101058374249863611565739225313693398799757656740287/100000000000000000000000000000000000000000000000000)⟩, ⟨1, (52640633834459410987246231670988417723/5000000000000000000000000000000000000000), 64, (101058374249863611565739225313693398799808185927411/100000000000000000000000000000000000000000000000000), (25264593562465902891434806328423349699952046481853/25000000000000000000000000000000000000000000000000)⟩, (50529187124931805782869612656846699399878828370143/50000000000000000000000000000000000000000000000000), (101058374249863611565739225313693398799757656740287/100000000000000000000000000000000000000000000000000), (101058374249863611565739225313693398799808185927411/100000000000000000000000000000000000000000000000000), (25264593562465902891434806328423349699952046481853/25000000000000000000000000000000000000000000000000)⟩
  logRoot := ⟨⟨1, (79038197017531729591459676867236843477/200000000000000000000000000000000000000), 64, (74233385661957090528519099947671376242787429111599/50000000000000000000000000000000000000000000000000), (148466771323914181057038199895342752485574858223199/100000000000000000000000000000000000000000000000000)⟩, ⟨1, (790381970175317295914596768672368434771/2000000000000000000000000000000000000000), 64, (7423338566195709052851909994767137624282454580443/5000000000000000000000000000000000000000000000000), (148466771323914181057038199895342752485649091608861/100000000000000000000000000000000000000000000000000)⟩, (74233385661957090528519099947671376242787429111599/50000000000000000000000000000000000000000000000000), (148466771323914181057038199895342752485574858223199/100000000000000000000000000000000000000000000000000), (7423338566195709052851909994767137624282454580443/5000000000000000000000000000000000000000000000000), (148466771323914181057038199895342752485649091608861/100000000000000000000000000000000000000000000000000)⟩

theorem checked : certificate.check=true := by decide +kernel

theorem activity_bounds {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    (certificate.a:ℝ)≤z ∧ z≤(Stage80MessageSourceData.Case056.parameters.upper:ℝ) := by
  have hl := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  have hu := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
  norm_num [certificate,interval,Stage80MessageSourceData.Case056.parameters,Stage80MessagePriceData.case056] at hl hu ⊢
  constructor <;> linarith

theorem actual_variance_of_source_valid
    (hsource : MessageSourceRowValid Stage80MessageSourceData.Case056.parameters.toReal
      Stage80MessageSourceData.Case056.parameters.lower Stage80MessageSourceData.Case056.parameters.upper)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 80≤S.card) (hN : S.card≤98) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hmean : hardCoreMean G S z=k)
    (hm : hardCoreAvailableMean G S B z≤(mhi:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept := by
  have hab := activity_bounds hz hq
  have hp := MessagePriceSpline.Parameters.check_sound Stage80MessageSourceData.Case056.parameters_checked
  have hlo : Stage80MessageSourceData.Case056.parameters.toReal.w=0 ∨ (Stage80MessageSourceData.Case056.parameters.lower:ℝ)≤z := by
    right
    norm_num [certificate,Stage80MessageSourceData.Case056.parameters,Stage80MessagePriceData.case056,interval] at hab ⊢; linarith
  have hv := hB.variance_le_mass_and_mean_with_log_bonus hG
    (Finset.card_pos.mp (by omega)) hp.1 hz hab.2 Stage80MessageSourceData.Case056.parameters.toReal hp.2.2.2.2 hp.2.2.1 hlo hsource
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
end ForestUnimodality.Stage80LogVarianceData.Cell059
