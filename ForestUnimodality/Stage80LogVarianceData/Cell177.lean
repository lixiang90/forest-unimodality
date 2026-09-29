import ForestUnimodality.LogVarianceProfileCertificate
import ForestUnimodality.Stage80KernelData.Cell177.Budget
import ForestUnimodality.Stage80MessageSourceData.Case054.Parameters

/-! Concrete scalar profile and graph conversion. Source validity is an explicit
premise until the independently checked message source is supplied. -/
namespace ForestUnimodality.Stage80LogVarianceData.Cell177
open Stage80KernelData.Cell177
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
  logNLo := (-1716748738278294565248328026421054491/200000000000000000000000000000000000000)
  logNHi := (-17167487382782945652483280264210544909/2000000000000000000000000000000000000000)
  logRootLo := (4266459301876114068824343245355777147367/10000000000000000000000000000000000000000)
  logRootHi := (1066614825469028517206085811338944286843/2500000000000000000000000000000000000000)
  logN := ⟨⟨1, (-1716748738278294565248328026421054491/200000000000000000000000000000000000000), 64, (49572649572649572649572649572649572649559556333523/50000000000000000000000000000000000000000000000000), (99145299145299145299145299145299145299119112667047/100000000000000000000000000000000000000000000000000)⟩, ⟨1, (-17167487382782945652483280264210544909/2000000000000000000000000000000000000000), 64, (99145299145299145299145299145299145299168685316619/100000000000000000000000000000000000000000000000000), (4957264957264957264957264957264957264958434265831/5000000000000000000000000000000000000000000000000)⟩, (49572649572649572649572649572649572649559556333523/50000000000000000000000000000000000000000000000000), (99145299145299145299145299145299145299119112667047/100000000000000000000000000000000000000000000000000), (99145299145299145299145299145299145299168685316619/100000000000000000000000000000000000000000000000000), (4957264957264957264957264957264957264958434265831/5000000000000000000000000000000000000000000000000)⟩
  logRoot := ⟨⟨1, (4266459301876114068824343245355777147367/10000000000000000000000000000000000000000), 64, (153211009174311926605504587155963302752251641200921/100000000000000000000000000000000000000000000000000), (76605504587155963302752293577981651376125820600461/50000000000000000000000000000000000000000000000000)⟩, ⟨1, (1066614825469028517206085811338944286843/2500000000000000000000000000000000000000), 64, (38302752293577981651376146788990825688082061676377/25000000000000000000000000000000000000000000000000), (153211009174311926605504587155963302752328246705509/100000000000000000000000000000000000000000000000000)⟩, (153211009174311926605504587155963302752251641200921/100000000000000000000000000000000000000000000000000), (76605504587155963302752293577981651376125820600461/50000000000000000000000000000000000000000000000000), (38302752293577981651376146788990825688082061676377/25000000000000000000000000000000000000000000000000), (153211009174311926605504587155963302752328246705509/100000000000000000000000000000000000000000000000000)⟩

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
end ForestUnimodality.Stage80LogVarianceData.Cell177
