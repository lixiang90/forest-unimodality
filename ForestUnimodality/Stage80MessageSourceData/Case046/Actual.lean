import ForestUnimodality.Stage80MessageSourceData.Case046.Complete

namespace ForestUnimodality.Stage80MessageSourceData.Case046
open MessagePriceSpline

theorem lower_eq : domain.lower=parameters.lower := by decide +kernel
theorem upper_eq : domain.b=parameters.upper := by decide +kernel

theorem actual_source_valid : MessageSourceRowValid parameters.toReal parameters.lower parameters.upper := by
  simpa only [lower_eq,upper_eq] using source_valid

variable {V : Type*} [DecidableEq V]

/-- True occupancy variance on every nonempty finite forest, throughout the
closed activity interval, including the one-component logarithmic bonus. -/
theorem actual_variance (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (hS : S.Nonempty) {z : ℝ} (hlo : (parameters.lower:ℝ)≤z) (hhi : z≤(parameters.upper:ℝ)) :
    hardCoreVariance G S z≤
      parameters.toReal.CJ*hardCoreMarginalSelectionScore G S z parameters.upper+
      parameters.toReal.Cmu*hardCoreMean G S z+
      (parameters.toReal.Dn-parameters.toReal.ell*Real.log (z/parameters.lower))*(S.card:ℝ)-
      parameters.toReal.ell*Real.log (1+z/(1+parameters.upper)) := by
  have hp := MessagePriceSpline.Parameters.check_sound parameters_checked
  exact forest_message_variance_with_log_bonus G hG S hS hp.1 (hp.1.trans_le hlo) hhi
    parameters.toReal hp.2.2.2.2 (Or.inr hlo) actual_source_valid

/-- The maximizing marginal independent set is the same one used by the
selection score and by the subsequent source window. -/
theorem actual_variance_le_mass {G : SimpleGraph V} {S I : Finset V} {z : ℝ}
    (hI : IsMaximumMarginalIndependentOn G S I z) (hG : G.IsAcyclic) (hS : S.Nonempty)
    (hlo : (parameters.lower:ℝ)≤z) (hhi : z≤(parameters.upper:ℝ)) :
    hardCoreVariance G S z≤
      (parameters.toReal.CJ+2*parameters.toReal.Cmu)*hardCoreOccupiedMass G S I z+
      (parameters.toReal.Dn-parameters.toReal.ell*Real.log (z/parameters.lower))*(S.card:ℝ)-
      parameters.toReal.ell*Real.log (1+z/(1+parameters.upper)) := by
  have hp := MessagePriceSpline.Parameters.check_sound parameters_checked
  exact hI.variance_le_mass_with_log_bonus hG hS hp.1 (hp.1.trans_le hlo) hhi parameters.toReal
    hp.2.2.2.2 hp.2.2.1 hp.2.2.2.1 (Or.inr hlo) actual_source_valid

#print axioms actual_source_valid
#print axioms actual_variance
#print axioms actual_variance_le_mass
end ForestUnimodality.Stage80MessageSourceData.Case046
