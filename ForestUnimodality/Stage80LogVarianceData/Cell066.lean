import ForestUnimodality.LogVarianceProfileCertificate
import ForestUnimodality.Stage80KernelData.Cell066.Budget
import ForestUnimodality.Stage80MessageSourceData.Case057.Parameters

/-! Concrete scalar profile and graph conversion. Source validity is an explicit
premise until the independently checked message source is supplied. -/
namespace ForestUnimodality.Stage80LogVarianceData.Cell066
open Stage80KernelData.Cell066
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def certificate : LogVarianceProfileCertificate.Certificate where
  qa := interval.lo
  qb := interval.hi
  a := interval.lo/(1-interval.lo)
  lower := Stage80MessageSourceData.Case057.parameters.lower
  b := Stage80MessageSourceData.Case057.parameters.upper
  C := Stage80MessageSourceData.Case057.parameters.CJ+2*Stage80MessageSourceData.Case057.parameters.Cmu
  Cmu := 0
  D := Stage80MessageSourceData.Case057.parameters.Dn
  ell := Stage80MessageSourceData.Case057.parameters.ell
  alpha := alpha
  beta := varianceIntercept
  nlo := 80
  nhi := 98
  rankUpper := 0
  logNLo := (-1/5000000000000000000000000000000000000000)
  logNHi := (1/5000000000000000000000000000000000000000)
  logRootLo := (3953127366441463747535166719987044548047/10000000000000000000000000000000000000000)
  logRootHi := (988281841610365936883791679996761137013/2500000000000000000000000000000000000000)
  logN := ⟨⟨1, (-1/5000000000000000000000000000000000000000), 64, (4999999999999999999999999999999999999999/5000000000000000000000000000000000000000), (99999999999999999999999999999999999999980000000001/100000000000000000000000000000000000000000000000000)⟩, ⟨1, (1/5000000000000000000000000000000000000000), 64, (5000000000000000000000000000000000000001/5000000000000000000000000000000000000000), (100000000000000000000000000000000000000020000000001/100000000000000000000000000000000000000000000000000)⟩, (4999999999999999999999999999999999999999/5000000000000000000000000000000000000000), (99999999999999999999999999999999999999980000000001/100000000000000000000000000000000000000000000000000), (5000000000000000000000000000000000000001/5000000000000000000000000000000000000000), (100000000000000000000000000000000000000020000000001/100000000000000000000000000000000000000000000000000)⟩
  logRoot := ⟨⟨1, (3953127366441463747535166719987044548047/10000000000000000000000000000000000000000), 64, (2969696969696969696969696969696969696968889071347/2000000000000000000000000000000000000000000000000), (148484848484848484848484848484848484848444453567351/100000000000000000000000000000000000000000000000000)⟩, ⟨1, (988281841610365936883791679996761137013/2500000000000000000000000000000000000000), 64, (148484848484848484848484848484848484848518695991593/100000000000000000000000000000000000000000000000000), (74242424242424242424242424242424242424259347995797/50000000000000000000000000000000000000000000000000)⟩, (2969696969696969696969696969696969696968889071347/2000000000000000000000000000000000000000000000000), (148484848484848484848484848484848484848444453567351/100000000000000000000000000000000000000000000000000), (148484848484848484848484848484848484848518695991593/100000000000000000000000000000000000000000000000000), (74242424242424242424242424242424242424259347995797/50000000000000000000000000000000000000000000000000)⟩

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
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 80≤S.card) (hN : S.card≤98) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept := by
  have hab := activity_bounds hz hq
  have hp := MessagePriceSpline.Parameters.check_sound Stage80MessageSourceData.Case057.parameters_checked
  have hlo : Stage80MessageSourceData.Case057.parameters.toReal.w=0 ∨ (Stage80MessageSourceData.Case057.parameters.lower:ℝ)≤z := by
    right
    norm_num [certificate,Stage80MessageSourceData.Case057.parameters,Stage80MessagePriceData.case057,interval] at hab ⊢; linarith
  have hv := hB.variance_le_mass_with_log_bonus hG
    (Finset.card_pos.mp (by omega)) hp.1 hz hab.2 Stage80MessageSourceData.Case057.parameters.toReal
    hp.2.2.2.2 hp.2.2.1 hp.2.2.2.1 hlo hsource
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz] at hv
  apply certificate.check_sound checked (z:=z) (n:=(S.card:ℝ)) (k:=0) hab.1 (by positivity)
    (by norm_num [certificate]; exact_mod_cast hn) (by norm_num [certificate]; exact_mod_cast hN)
    (hardCoreAvailableMean_nonneg G S B hz.le)
    (by norm_num [certificate]) hq
  simpa only [certificate,MessagePriceSpline.Parameters.toReal,Rat.cast_add,Rat.cast_mul,
    Rat.cast_ofNat,Rat.cast_zero,zero_mul,add_zero] using hv

#print axioms checked
#print axioms activity_bounds
#print axioms actual_variance_of_source_valid
end ForestUnimodality.Stage80LogVarianceData.Cell066
