import ForestUnimodality.Stage59KernelData.Cell063.Budget
import ForestUnimodality.Stage80MessageSourceData.Case004.Parameters
import ForestUnimodality.LogVarianceProfile
import ForestUnimodality.LaplaceRateInterval

/-! Conditional on the complete source row; not a source-validity proof. -/
namespace ForestUnimodality.Stage59KernelData.Cell063
variable {V : Type*} [DecidableEq V]

theorem message_profile_variance
    (hsource : MessageSourceRowValid Stage80MessageSourceData.Case004.parameters.toReal
      Stage80MessageSourceData.Case004.parameters.lower Stage80MessageSourceData.Case004.parameters.upper)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 59≤S.card) (hN : S.card≤79) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc ((9287/19012):ℝ) ((24/49):ℝ))
    (ha : ((9287/9725):ℝ)≤z) (hb : z≤((24/25):ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+
        (0:ℝ) := by
  have hp := MessagePriceSpline.Parameters.check_sound Stage80MessageSourceData.Case004.parameters_checked
  have hs : S.Nonempty := Finset.card_pos.mp (by omega)
  have hlo : (Stage80MessageSourceData.Case004.parameters.lower:ℝ)≤z := by
    norm_num [Stage80MessageSourceData.Case004.parameters, Stage80MessagePriceData.case004, MessagePriceSpline.Parameters.toReal]
    linarith
  have hhi : z≤(Stage80MessageSourceData.Case004.parameters.upper:ℝ) := by
    norm_num [Stage80MessageSourceData.Case004.parameters, Stage80MessagePriceData.case004, MessagePriceSpline.Parameters.toReal]
    linarith
  have hv := hB.variance_le_mass_with_log_bonus hG hs hp.1 hz hhi
    Stage80MessageSourceData.Case004.parameters.toReal hp.2.2.2.2 hp.2.2.1 hp.2.2.2.1 (Or.inr hlo) hsource
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz] at hv
  have hlin : hardCoreVariance G S z≤((887807994529/1000000000000):ℝ)*
      (z/(1+z)*hardCoreAvailableMean G S B z)+((0/1):ℝ)*(S.card:ℝ) := by
    norm_num [Stage80MessageSourceData.Case004.parameters, Stage80MessagePriceData.case004, MessagePriceSpline.Parameters.toReal] at hv ⊢
    exact hv
  have hcoef := quadratic_profile_of_endpoints (C:=((887807994529/1000000000000):ℝ)) hq
    (show ((887807994529/1000000000000):ℝ)*(9287/19012)-(9287/19012)*(1-(9287/19012))≤(alpha:ℝ) by norm_num [alpha])
    (show ((887807994529/1000000000000):ℝ)*(24/49)-(24/49)*(1-(24/49))≤(alpha:ℝ) by norm_num [alpha])
  have hm := mul_le_mul_of_nonneg_right hcoef (hardCoreAvailableMean_nonneg G S B hz.le)
  have hnR : (S.card:ℝ)≤79 := by exact_mod_cast hN
  have hintercept : ((0/1):ℝ)*(S.card:ℝ)≤(0:ℝ) := by
    norm_num
  nlinarith

#print axioms message_profile_variance
end ForestUnimodality.Stage59KernelData.Cell063
