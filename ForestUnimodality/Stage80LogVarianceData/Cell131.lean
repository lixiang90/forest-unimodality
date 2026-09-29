import ForestUnimodality.LogVarianceProfileCertificate
import ForestUnimodality.Stage80KernelData.Cell131.Budget
import ForestUnimodality.Stage80MessageSourceData.Case052.Parameters

/-! Concrete scalar profile and graph conversion. Source validity is an explicit
premise until the independently checked message source is supplied. -/
namespace ForestUnimodality.Stage80LogVarianceData.Cell131
open Stage80KernelData.Cell131
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def certificate : LogVarianceProfileCertificate.Certificate where
  qa := interval.lo
  qb := interval.hi
  a := interval.lo/(1-interval.lo)
  lower := Stage80MessageSourceData.Case052.parameters.lower
  b := Stage80MessageSourceData.Case052.parameters.upper
  C := Stage80MessageSourceData.Case052.parameters.CJ
  Cmu := Stage80MessageSourceData.Case052.parameters.Cmu
  D := Stage80MessageSourceData.Case052.parameters.Dn
  ell := Stage80MessageSourceData.Case052.parameters.ell
  alpha := alpha
  beta := varianceIntercept
  nlo := 80
  nhi := 98
  rankUpper := 23
  logNLo := (-22730763206936474535682071968321189309/10000000000000000000000000000000000000000)
  logNHi := (-2841345400867059316960258996040148663/1250000000000000000000000000000000000000)
  logRootLo := (4195470828587601248185748554023059725219/10000000000000000000000000000000000000000)
  logRootHi := (524433853573450156023218569252882465653/1250000000000000000000000000000000000000)
  logN := ⟨⟨1, (-22730763206936474535682071968321189309/10000000000000000000000000000000000000000), 64, (24943237629023687219207420170367626930317510800607/25000000000000000000000000000000000000000000000000), (99772950516094748876829680681470507721270043202429/100000000000000000000000000000000000000000000000000)⟩, ⟨1, (-2841345400867059316960258996040148663/1250000000000000000000000000000000000000), 64, (49886475258047374438414840340735253860659964838843/50000000000000000000000000000000000000000000000000), (99772950516094748876829680681470507721319929677687/100000000000000000000000000000000000000000000000000)⟩, (24943237629023687219207420170367626930317510800607/25000000000000000000000000000000000000000000000000), (99772950516094748876829680681470507721270043202429/100000000000000000000000000000000000000000000000000), (49886475258047374438414840340735253860659964838843/50000000000000000000000000000000000000000000000000), (99772950516094748876829680681470507721319929677687/100000000000000000000000000000000000000000000000000)⟩
  logRoot := ⟨⟨1, (4195470828587601248185748554023059725219/10000000000000000000000000000000000000000), 64, (76063619461060212177044160083457425775877358508913/50000000000000000000000000000000000000000000000000), (152127238922120424354088320166914851551754717017827/100000000000000000000000000000000000000000000000000)⟩, ⟨1, (524433853573450156023218569252882465653/1250000000000000000000000000000000000000), 64, (152127238922120424354088320166914851551830780637287/100000000000000000000000000000000000000000000000000), (19015904865265053044261040020864356443978847579661/12500000000000000000000000000000000000000000000000)⟩, (76063619461060212177044160083457425775877358508913/50000000000000000000000000000000000000000000000000), (152127238922120424354088320166914851551754717017827/100000000000000000000000000000000000000000000000000), (152127238922120424354088320166914851551830780637287/100000000000000000000000000000000000000000000000000), (19015904865265053044261040020864356443978847579661/12500000000000000000000000000000000000000000000000)⟩

theorem checked : certificate.check=true := by decide +kernel

theorem activity_bounds {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    (certificate.a:ℝ)≤z ∧ z≤(Stage80MessageSourceData.Case052.parameters.upper:ℝ) := by
  have hl := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  have hu := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
  norm_num [certificate,interval,Stage80MessageSourceData.Case052.parameters,Stage80MessagePriceData.case052] at hl hu ⊢
  constructor <;> linarith

theorem actual_variance_of_source_valid
    (hsource : MessageSourceRowValid Stage80MessageSourceData.Case052.parameters.toReal
      Stage80MessageSourceData.Case052.parameters.lower Stage80MessageSourceData.Case052.parameters.upper)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 80≤S.card) (hN : S.card≤98) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hmean : hardCoreMean G S z=k)
    (hm : hardCoreAvailableMean G S B z≤(mhi:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept := by
  have hab := activity_bounds hz hq
  have hp := MessagePriceSpline.Parameters.check_sound Stage80MessageSourceData.Case052.parameters_checked
  have hlo : Stage80MessageSourceData.Case052.parameters.toReal.w=0 ∨ (Stage80MessageSourceData.Case052.parameters.lower:ℝ)≤z := by
    left
    norm_num [Stage80MessageSourceData.Case052.parameters,Stage80MessagePriceData.case052,MessagePriceSpline.Parameters.toReal]
  have hv := hB.variance_le_mass_and_mean_with_log_bonus hG
    (Finset.card_pos.mp (by omega)) hp.1 hz hab.2 Stage80MessageSourceData.Case052.parameters.toReal hp.2.2.2.2 hp.2.2.1 hlo hsource
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
end ForestUnimodality.Stage80LogVarianceData.Cell131
