import ForestUnimodality.TiltedSourceData.Case20.Complete
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.TiltedSourceData.Case20
variable {V : Type*} [DecidableEq V]

/-- A fixed independent set throughout the entire exponential tilt step. -/
theorem actual_variance (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V)
    (hB : G.IsIndepSet (B:Set V)) {z start t : ℝ} (hz : 0<z)
    (hzcap : z≤(domain0.b:ℝ)) (hstart : z*Real.exp (-start)≤(domain1.b:ℝ)) (ht : start≤t) :
    FixedIndependentTilt.markedVariance G S B z t≤
      parameters.toReal.C*FixedIndependentTilt.markedMean G S B z t :=
  forest_fixed_independent_tilt_variance G hG S B hB hz
    (ParametricSource.Domain.check_sound domain0_checked).b_pos
    (ParametricSource.Domain.check_sound domain1_checked).b_pos hzcap hstart
    parameters.toReal (TiltedSource.Parameters.check_sound parameters_checked).1 source_valid t ht

#print axioms actual_variance
end ForestUnimodality.TiltedSourceData.Case20
