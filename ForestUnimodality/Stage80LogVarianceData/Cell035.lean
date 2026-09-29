import ForestUnimodality.LogVarianceProfileCertificate
import ForestUnimodality.Stage80KernelData.Cell035.Budget
import ForestUnimodality.Stage80MessageSourceData.Case064.Parameters

/-! Concrete scalar profile and graph conversion. Source validity is an explicit
premise until the independently checked message source is supplied. -/
namespace ForestUnimodality.Stage80LogVarianceData.Cell035
open Stage80KernelData.Cell035
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
  logNLo := (55577989198086924524126236994568106263/10000000000000000000000000000000000000000)
  logNHi := (13894497299521731131031559248642026567/2500000000000000000000000000000000000000)
  logRootLo := (3859639849850763789727707819835792924537/10000000000000000000000000000000000000000)
  logRootHi := (1929819924925381894863853909917896462271/5000000000000000000000000000000000000000)
  logN := ⟨⟨1, (55577989198086924524126236994568106263/10000000000000000000000000000000000000000), 64, (100557327213661967633296575567013381813826148660861/100000000000000000000000000000000000000000000000000), (50278663606830983816648287783506690906913074330431/50000000000000000000000000000000000000000000000000)⟩, ⟨1, (13894497299521731131031559248642026567/2500000000000000000000000000000000000000), 64, (25139331803415491908324143891753345453469106831117/25000000000000000000000000000000000000000000000000), (100557327213661967633296575567013381813876427324469/100000000000000000000000000000000000000000000000000)⟩, (100557327213661967633296575567013381813826148660861/100000000000000000000000000000000000000000000000000), (50278663606830983816648287783506690906913074330431/50000000000000000000000000000000000000000000000000), (25139331803415491908324143891753345453469106831117/25000000000000000000000000000000000000000000000000), (100557327213661967633296575567013381813876427324469/100000000000000000000000000000000000000000000000000)⟩
  logRoot := ⟨⟨1, (3859639849850763789727707819835792924537/10000000000000000000000000000000000000000), 64, (73551584531620829261482619014379449951117551620517/50000000000000000000000000000000000000000000000000), (29420633812648331704593047605751779980447020648207/20000000000000000000000000000000000000000000000000)⟩, ⟨1, (1929819924925381894863853909917896462271/5000000000000000000000000000000000000000), 64, (73551584531620829261482619014379449951154327412783/50000000000000000000000000000000000000000000000000), (147103169063241658522965238028758899902308654825567/100000000000000000000000000000000000000000000000000)⟩, (73551584531620829261482619014379449951117551620517/50000000000000000000000000000000000000000000000000), (29420633812648331704593047605751779980447020648207/20000000000000000000000000000000000000000000000000), (73551584531620829261482619014379449951154327412783/50000000000000000000000000000000000000000000000000), (147103169063241658522965238028758899902308654825567/100000000000000000000000000000000000000000000000000)⟩

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
end ForestUnimodality.Stage80LogVarianceData.Cell035
