import ForestUnimodality.LogVarianceProfileCertificate
import ForestUnimodality.Stage80KernelData.Cell053.Budget
import ForestUnimodality.Stage80MessageSourceData.Case056.Parameters

/-! Concrete scalar profile and graph conversion. Source validity is an explicit
premise until the independently checked message source is supplied. -/
namespace ForestUnimodality.Stage80LogVarianceData.Cell053
open Stage80KernelData.Cell053
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
  logNLo := (6580569321413770328099410819343189111/1250000000000000000000000000000000000000)
  logNHi := (52644554571310162624795286554745512893/10000000000000000000000000000000000000000)
  logRootLo := (61480579853638145615292380440880711021/156250000000000000000000000000000000000)
  logRootHi := (3934757110632841319378712348216365505349/10000000000000000000000000000000000000000)
  logN := ⟨⟨1, (6580569321413770328099410819343189111/1250000000000000000000000000000000000000), 64, (50263916852587473472275126516841704304278487560189/50000000000000000000000000000000000000000000000000), (100527833705174946944550253033683408608556975120379/100000000000000000000000000000000000000000000000000)⟩, ⟨1, (52644554571310162624795286554745512893/10000000000000000000000000000000000000000), 64, (10052783370517494694455025303368340860860723903723/10000000000000000000000000000000000000000000000000), (100527833705174946944550253033683408608607239037231/100000000000000000000000000000000000000000000000000)⟩, (50263916852587473472275126516841704304278487560189/50000000000000000000000000000000000000000000000000), (100527833705174946944550253033683408608556975120379/100000000000000000000000000000000000000000000000000), (10052783370517494694455025303368340860860723903723/10000000000000000000000000000000000000000000000000), (100527833705174946944550253033683408608607239037231/100000000000000000000000000000000000000000000000000)⟩
  logRoot := ⟨⟨1, (61480579853638145615292380440880711021/156250000000000000000000000000000000000), 64, (74106164204812359726499295370322041860203352278771/50000000000000000000000000000000000000000000000000), (148212328409624719452998590740644083720406704557543/100000000000000000000000000000000000000000000000000)⟩, ⟨1, (3934757110632841319378712348216365505349/10000000000000000000000000000000000000000), 64, (74106164204812359726499295370322041860240405360873/50000000000000000000000000000000000000000000000000), (148212328409624719452998590740644083720480810721747/100000000000000000000000000000000000000000000000000)⟩, (74106164204812359726499295370322041860203352278771/50000000000000000000000000000000000000000000000000), (148212328409624719452998590740644083720406704557543/100000000000000000000000000000000000000000000000000), (74106164204812359726499295370322041860240405360873/50000000000000000000000000000000000000000000000000), (148212328409624719452998590740644083720480810721747/100000000000000000000000000000000000000000000000000)⟩

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
end ForestUnimodality.Stage80LogVarianceData.Cell053
