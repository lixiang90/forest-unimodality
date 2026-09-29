import ForestUnimodality.LogVarianceProfileCertificate
import ForestUnimodality.Stage80KernelData.Cell032.Budget
import ForestUnimodality.Stage80MessageSourceData.Case064.Parameters

/-! Concrete scalar profile and graph conversion. Source validity is an explicit
premise until the independently checked message source is supplied. -/
namespace ForestUnimodality.Stage80LogVarianceData.Cell032
open Stage80KernelData.Cell032
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def certificate : LogVarianceProfileCertificate.Certificate where
  qa := interval.lo
  qb := interval.hi
  a := interval.lo/(1-interval.lo)
  lower := Stage80MessageSourceData.Case064.parameters.lower
  b := Stage80MessageSourceData.Case064.parameters.upper
  C := Stage80MessageSourceData.Case064.parameters.CJ
  Cmu := Stage80MessageSourceData.Case064.parameters.Cmu
  D := Stage80MessageSourceData.Case064.parameters.Dn
  ell := Stage80MessageSourceData.Case064.parameters.ell
  alpha := alpha
  beta := varianceIntercept
  nlo := 80
  nhi := 98
  rankUpper := 22
  logNLo := (-148628162107924517840885035605190797/2500000000000000000000000000000000000000)
  logNHi := (-594512648431698071363540142420763183/10000000000000000000000000000000000000000)
  logRootLo := (768337490608773885967966930342518056671/2000000000000000000000000000000000000000)
  logRootHi := (24010546581524183936498966573203689271/62500000000000000000000000000000000000)
  logN := ⟨⟨1, (-148628162107924517840885035605190797/2500000000000000000000000000000000000000), 64, (124992568812793531894655490161108138636202192853/125000000000000000000000000000000000000000000000), (99994055050234825515724392128886510908961754282401/100000000000000000000000000000000000000000000000000)⟩, ⟨1, (-594512648431698071363540142420763183/10000000000000000000000000000000000000000), 64, (49997027525117412757862196064443255454505875654963/50000000000000000000000000000000000000000000000000), (99994055050234825515724392128886510909011751309927/100000000000000000000000000000000000000000000000000)⟩, (124992568812793531894655490161108138636202192853/125000000000000000000000000000000000000000000000), (99994055050234825515724392128886510908961754282401/100000000000000000000000000000000000000000000000000), (49997027525117412757862196064443255454505875654963/50000000000000000000000000000000000000000000000000), (99994055050234825515724392128886510909011751309927/100000000000000000000000000000000000000000000000000)⟩
  logRoot := ⟨⟨1, (768337490608773885967966930342518056671/2000000000000000000000000000000000000000), 64, (73419660261765524923419660261765524923397794972319/50000000000000000000000000000000000000000000000000), (146839320523531049846839320523531049846795589944639/100000000000000000000000000000000000000000000000000)⟩, ⟨1, (24010546581524183936498966573203689271/62500000000000000000000000000000000000), 64, (1468393205235310498468393205235310498468690096049/1000000000000000000000000000000000000000000000000), (146839320523531049846839320523531049846869009604901/100000000000000000000000000000000000000000000000000)⟩, (73419660261765524923419660261765524923397794972319/50000000000000000000000000000000000000000000000000), (146839320523531049846839320523531049846795589944639/100000000000000000000000000000000000000000000000000), (1468393205235310498468393205235310498468690096049/1000000000000000000000000000000000000000000000000), (146839320523531049846839320523531049846869009604901/100000000000000000000000000000000000000000000000000)⟩

theorem checked : certificate.check=true := by decide +kernel

theorem activity_bounds {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    (certificate.a:ℝ)≤z ∧ z≤(Stage80MessageSourceData.Case064.parameters.upper:ℝ) := by
  have hl := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  have hu := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
  norm_num [certificate,interval,Stage80MessageSourceData.Case064.parameters,Stage80MessagePriceData.case064] at hl hu ⊢
  constructor <;> linarith

theorem actual_variance_of_source_valid
    (hsource : MessageSourceRowValid Stage80MessageSourceData.Case064.parameters.toReal
      Stage80MessageSourceData.Case064.parameters.lower Stage80MessageSourceData.Case064.parameters.upper)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 80≤S.card) (hN : S.card≤98) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hmean : hardCoreMean G S z=k)
    (hm : hardCoreAvailableMean G S B z≤(mhi:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept := by
  have hab := activity_bounds hz hq
  have hp := MessagePriceSpline.Parameters.check_sound Stage80MessageSourceData.Case064.parameters_checked
  have hlo : Stage80MessageSourceData.Case064.parameters.toReal.w=0 ∨ (Stage80MessageSourceData.Case064.parameters.lower:ℝ)≤z := by
    left
    norm_num [Stage80MessageSourceData.Case064.parameters,Stage80MessagePriceData.case064,MessagePriceSpline.Parameters.toReal]
  have hv := hB.variance_le_mass_and_mean_with_log_bonus hG
    (Finset.card_pos.mp (by omega)) hp.1 hz hab.2 Stage80MessageSourceData.Case064.parameters.toReal hp.2.2.2.2 hp.2.2.1 hlo hsource
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz,hmean] at hv
  have hk : k≤22 := integer_rank_upper_of_available_mean hB hG hz
    (by norm_num [interval]) hq.2 hm hmean (by norm_num [interval,mhi])
  exact certificate.check_sound checked hab.1 (by positivity)
    (by norm_num [certificate]; exact_mod_cast hn) (by norm_num [certificate]; exact_mod_cast hN)
    (hardCoreAvailableMean_nonneg G S B hz.le)
    (by norm_num [certificate]; exact_mod_cast hk) hq hv

#print axioms checked
#print axioms activity_bounds
#print axioms actual_variance_of_source_valid
end ForestUnimodality.Stage80LogVarianceData.Cell032
