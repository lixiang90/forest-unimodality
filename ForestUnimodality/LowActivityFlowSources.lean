import ForestUnimodality.AffineSourceLibrary
import ForestUnimodality.TiltedSourceData.Case03.Actual
import ForestUnimodality.TiltedSourceData.Case05.Actual
import ForestUnimodality.TiltedSourceData.Case31.Actual
import ForestUnimodality.TiltedSourceData.Case32.Actual
import ForestUnimodality.TiltedSourceData.Case33.Actual

/-! Exactly the six sources selected by the first two low-activity flow
chains. A source is valid throughout the closed step for the same fixed B. -/
namespace ForestUnimodality.LowActivityFlowSources
abbrev Source := Fin 6

def A : Source→ℚ := ![AffineSourceData.Case01.parameters.A,0,0,0,0,0]
def C : Source→ℚ := ![AffineSourceData.Case01.parameters.C,
  TiltedSourceData.Case03.parameters.C,TiltedSourceData.Case05.parameters.C,
  TiltedSourceData.Case31.parameters.C,TiltedSourceData.Case32.parameters.C,
  TiltedSourceData.Case33.parameters.C]
def b0 : Source→ℚ := ![AffineSourceData.Case01.domain.b,
  TiltedSourceData.Case03.domain0.b,TiltedSourceData.Case05.domain0.b,
  TiltedSourceData.Case31.domain0.b,TiltedSourceData.Case32.domain0.b,
  TiltedSourceData.Case33.domain0.b]
def b1 : Source→ℚ := ![0,
  TiltedSourceData.Case03.domain1.b,TiltedSourceData.Case05.domain1.b,
  TiltedSourceData.Case31.domain1.b,TiltedSourceData.Case32.domain1.b,
  TiltedSourceData.Case33.domain1.b]

theorem C_pos (i : Source) : (0:ℝ)<C i := by
  fin_cases i
  · exact AffineSourceLibrary.C_pos 0
  · exact (TiltedSource.Parameters.check_sound TiltedSourceData.Case03.parameters_checked).2
  · exact (TiltedSource.Parameters.check_sound TiltedSourceData.Case05.parameters_checked).2
  · exact (TiltedSource.Parameters.check_sound TiltedSourceData.Case31.parameters_checked).2
  · exact (TiltedSource.Parameters.check_sound TiltedSourceData.Case32.parameters_checked).2
  · exact (TiltedSource.Parameters.check_sound TiltedSourceData.Case33.parameters_checked).2

variable {V : Type*} [DecidableEq V]

theorem actual_variance (i : Source) (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S B : Finset V) (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V))
    {z start t m beta : ℝ} (hz : 0<z) (hstart : 0≤start) (ht : start≤t)
    (hzcap : z≤(b0 i:ℝ)) (hmarked : i≠0 → z*Real.exp (-start)≤(b1 i:ℝ))
    (hcard : (B.card:ℝ)≤m*beta) :
    FixedIndependentTilt.markedVariance G S B z t≤
      m*((A i:ℝ)*beta)+(C i:ℝ)*FixedIndependentTilt.markedMean G S B z t := by
  fin_cases i
  · have hh := AffineSourceLibrary.actual_tilt 0 G hG S B hBS hz hzcap t (hstart.trans ht)
    have hA := (AffineSource.Parameters.check_sound AffineSourceData.Case01.parameters_checked).2.1
    have hbound := mul_le_mul_of_nonneg_left hcard hA
    have hins : FixedIndependentTilt.inside B=(fun J : Finset V=>((J∩B).card:ℝ)) := rfl
    have hv : FixedIndependentTilt.markedVariance G S B z t≤
        (AffineSourceData.Case01.parameters.A:ℝ)*(B.card:ℝ)+
        (AffineSourceData.Case01.parameters.C:ℝ)*FixedIndependentTilt.markedMean G S B z t := by
      simpa [FixedIndependentTilt.markedVariance,FixedIndependentTilt.markedMean,
        FixedIndependentTilt.weight_eq_heterogeneous,heterogeneousVariance,heterogeneousMean,
        hins,AffineSourceLibrary.parameters] using hh
    change (AffineSourceData.Case01.parameters.A:ℝ)*(B.card:ℝ)≤
      (AffineSourceData.Case01.parameters.A:ℝ)*(m*beta) at hbound
    change FixedIndependentTilt.markedVariance G S B z t≤
      m*((AffineSourceData.Case01.parameters.A:ℝ)*beta)+
      (AffineSourceData.Case01.parameters.C:ℝ)*FixedIndependentTilt.markedMean G S B z t
    nlinarith
  · have hh := TiltedSourceData.Case03.actual_variance G hG S B hB hz hzcap (hmarked (by decide)) ht
    simpa [A,C,TiltedSource.Parameters.toReal] using hh
  · have hh := TiltedSourceData.Case05.actual_variance G hG S B hB hz hzcap (hmarked (by decide)) ht
    simpa [A,C,TiltedSource.Parameters.toReal] using hh
  · have hh := TiltedSourceData.Case31.actual_variance G hG S B hB hz hzcap (hmarked (by decide)) ht
    simpa [A,C,TiltedSource.Parameters.toReal] using hh
  · have hh := TiltedSourceData.Case32.actual_variance G hG S B hB hz hzcap (hmarked (by decide)) ht
    simpa [A,C,TiltedSource.Parameters.toReal] using hh
  · have hh := TiltedSourceData.Case33.actual_variance G hG S B hB hz hzcap (hmarked (by decide)) ht
    simpa [A,C,TiltedSource.Parameters.toReal] using hh

#print axioms C_pos
#print axioms actual_variance
end ForestUnimodality.LowActivityFlowSources
