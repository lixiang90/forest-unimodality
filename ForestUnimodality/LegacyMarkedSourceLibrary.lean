import ForestUnimodality.SourceCertifiedLibrary

import ForestUnimodality.FixedIndependentFlow

namespace ForestUnimodality.LegacyMarkedSourceLibrary

open Set

def firstParameters : RationalSourceParameters := ⟨(14896533/50000000), (3577121/5000000), (1729251/5000000), (10854739/50000000), (24188011/100000000), (11742489/25000000), 0, (96780649/100000000), (89615257/100000000), (240111/2000000)⟩

def parameters : Fin 10→RationalSourceParameters := ![firstParameters, ParametricSourceData.Case02.parameters, ParametricSourceData.Case03.parameters, ParametricSourceData.Case04.parameters, ParametricSourceData.Case05.parameters, ParametricSourceData.Case06.parameters, ParametricSourceData.Case07.parameters, ParametricSourceData.Case08.parameters, ParametricSourceData.Case09.parameters, ParametricSourceData.Case10.parameters]

def lower : Fin 10→ℚ := ![22/25, ParametricSourceData.Case02.domain.lower, ParametricSourceData.Case03.domain.lower, ParametricSourceData.Case04.domain.lower, ParametricSourceData.Case05.domain.lower, ParametricSourceData.Case06.domain.lower, ParametricSourceData.Case07.domain.lower, ParametricSourceData.Case08.domain.lower, ParametricSourceData.Case09.domain.lower, ParametricSourceData.Case10.domain.lower]

def upper : Fin 10→ℚ := ![1, ParametricSourceData.Case02.domain.b, ParametricSourceData.Case03.domain.b, ParametricSourceData.Case04.domain.b, ParametricSourceData.Case05.domain.b, ParametricSourceData.Case06.domain.b, ParametricSourceData.Case07.domain.b, ParametricSourceData.Case08.domain.b, ParametricSourceData.Case09.domain.b, ParametricSourceData.Case10.domain.b]

theorem parameters_checked (i : Fin 10) : (parameters i).admissibleCheck=true := by

  fin_cases i

  · decide +kernel

  · exact ParametricSourceData.Case02.parameters_checked

  · exact ParametricSourceData.Case03.parameters_checked

  · exact ParametricSourceData.Case04.parameters_checked

  · exact ParametricSourceData.Case05.parameters_checked

  · exact ParametricSourceData.Case06.parameters_checked

  · exact ParametricSourceData.Case07.parameters_checked

  · exact ParametricSourceData.Case08.parameters_checked

  · exact ParametricSourceData.Case09.parameters_checked

  · exact ParametricSourceData.Case10.parameters_checked

theorem lower_pos (i : Fin 10) : (0:ℝ)<lower i := by

  fin_cases i

  · norm_num [lower]

  · exact (ParametricSource.Domain.check_sound ParametricSourceData.Case02.domain_checked).lower_pos

  · exact (ParametricSource.Domain.check_sound ParametricSourceData.Case03.domain_checked).lower_pos

  · exact (ParametricSource.Domain.check_sound ParametricSourceData.Case04.domain_checked).lower_pos

  · exact (ParametricSource.Domain.check_sound ParametricSourceData.Case05.domain_checked).lower_pos

  · exact (ParametricSource.Domain.check_sound ParametricSourceData.Case06.domain_checked).lower_pos

  · exact (ParametricSource.Domain.check_sound ParametricSourceData.Case07.domain_checked).lower_pos

  · exact (ParametricSource.Domain.check_sound ParametricSourceData.Case08.domain_checked).lower_pos

  · exact (ParametricSource.Domain.check_sound ParametricSourceData.Case09.domain_checked).lower_pos

  · exact (ParametricSource.Domain.check_sound ParametricSourceData.Case10.domain_checked).lower_pos

theorem source_valid (i : Fin 10) : SourceRowValid (parameters i).toReal (lower i) (upper i) := by

  fin_cases i

  · convert sourceRowValid_22_25_1 using 1 <;>

      norm_num [parameters,lower,upper,firstParameters,RationalSourceParameters.toReal,sourceParameters_22_25_1]

  · exact ParametricSourceData.Case02.source_valid

  · exact ParametricSourceData.Case03.source_valid

  · exact ParametricSourceData.Case04.source_valid

  · exact ParametricSourceData.Case05.source_valid

  · exact ParametricSourceData.Case06.source_valid

  · exact ParametricSourceData.Case07.source_valid

  · exact ParametricSourceData.Case08.source_valid

  · exact ParametricSourceData.Case09.source_valid

  · exact ParametricSourceData.Case10.source_valid

theorem coefficients_nonneg (i : Fin 10) : 0≤((parameters i).A:ℝ) ∧ 0≤((parameters i).C:ℝ) := by

  fin_cases i <;> norm_num [parameters,firstParameters,ParametricSourceData.Case02.parameters, ParametricSourceData.Case03.parameters, ParametricSourceData.Case04.parameters, ParametricSourceData.Case05.parameters, ParametricSourceData.Case06.parameters, ParametricSourceData.Case07.parameters, ParametricSourceData.Case08.parameters, ParametricSourceData.Case09.parameters, ParametricSourceData.Case10.parameters]

variable {V : Type*} [DecidableEq V]
theorem variance_on_step (i : Fin 10) (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S B : Finset V) (hB : G.IsIndepSet (B:Set V)) {z a b start finish m U : ℝ}
    (ha : 0<a) (hzlo : a≤z) (hzhi : z≤b) (hstart : 0≤start)
    (hlo : (lower i:ℝ)≤a*Real.exp (-finish)) (hhi : b≤(upper i:ℝ))
    (hmu : ∀t∈Icc start finish, FixedIndependentTilt.totalMean G S B z t≤m*U) :
    ∀t∈Icc start finish, FixedIndependentTilt.markedVariance G S B z t≤
      m*(((parameters i).A:ℝ)*U)+((parameters i).C:ℝ)*FixedIndependentTilt.markedMean G S B z t :=
  FixedIndependentTilt.marked_source_on_step G hG S B hB ha hzlo hzhi hstart
    (lower_pos i) hlo hhi (parameters i).toReal
    ((parameters i).admissible_sound (parameters_checked i))
    (coefficients_nonneg i).1 (source_valid i) hmu
#print axioms source_valid
#print axioms variance_on_step
end ForestUnimodality.LegacyMarkedSourceLibrary
