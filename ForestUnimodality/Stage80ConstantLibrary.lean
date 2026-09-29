import ForestUnimodality.Stage80ConstantData.Case23.Complete
import ForestUnimodality.Stage80ConstantData.Case24.Complete
import ForestUnimodality.Stage80ConstantData.Case25.Complete
import ForestUnimodality.Stage80ConstantData.Case26.Complete
import ForestUnimodality.Stage80ConstantData.Case27.Complete
import ForestUnimodality.Stage80ConstantData.Case28.Complete
import ForestUnimodality.Stage80ConstantData.Case29.Complete
import ForestUnimodality.Stage80ConstantData.Case30.Complete
import ForestUnimodality.Stage80ConstantData.Case31.Complete
import ForestUnimodality.Stage80ConstantData.Case32.Complete
import ForestUnimodality.Stage80ConstantData.Case33.Complete
import ForestUnimodality.Stage80ConstantData.Case34.Complete
import ForestUnimodality.Stage80ConstantData.Case35.Complete
import ForestUnimodality.Stage80ConstantData.Case36.Complete
import ForestUnimodality.Stage80ConstantData.Case37.Complete
import ForestUnimodality.Stage80ConstantData.Case38.Complete
import ForestUnimodality.Stage80ConstantData.Case39.Complete
import ForestUnimodality.Stage80ConstantData.Case40.Complete
import ForestUnimodality.Stage80ConstantData.Case41.Complete
import ForestUnimodality.Stage80ConstantData.Case42.Complete

namespace ForestUnimodality.Stage80ConstantLibrary

def parameters : Fin 20 → SelectionSource.Parameters := ![Stage80ConstantData.Case23.parameters, Stage80ConstantData.Case24.parameters, Stage80ConstantData.Case25.parameters, Stage80ConstantData.Case26.parameters, Stage80ConstantData.Case27.parameters, Stage80ConstantData.Case28.parameters, Stage80ConstantData.Case29.parameters, Stage80ConstantData.Case30.parameters, Stage80ConstantData.Case31.parameters, Stage80ConstantData.Case32.parameters, Stage80ConstantData.Case33.parameters, Stage80ConstantData.Case34.parameters, Stage80ConstantData.Case35.parameters, Stage80ConstantData.Case36.parameters, Stage80ConstantData.Case37.parameters, Stage80ConstantData.Case38.parameters, Stage80ConstantData.Case39.parameters, Stage80ConstantData.Case40.parameters, Stage80ConstantData.Case41.parameters, Stage80ConstantData.Case42.parameters]
def domain : Fin 20 → SelectionSource.Domain := ![Stage80ConstantData.Case23.domain, Stage80ConstantData.Case24.domain, Stage80ConstantData.Case25.domain, Stage80ConstantData.Case26.domain, Stage80ConstantData.Case27.domain, Stage80ConstantData.Case28.domain, Stage80ConstantData.Case29.domain, Stage80ConstantData.Case30.domain, Stage80ConstantData.Case31.domain, Stage80ConstantData.Case32.domain, Stage80ConstantData.Case33.domain, Stage80ConstantData.Case34.domain, Stage80ConstantData.Case35.domain, Stage80ConstantData.Case36.domain, Stage80ConstantData.Case37.domain, Stage80ConstantData.Case38.domain, Stage80ConstantData.Case39.domain, Stage80ConstantData.Case40.domain, Stage80ConstantData.Case41.domain, Stage80ConstantData.Case42.domain]

def factor (i : Fin 20) : ℚ := (parameters i).CJ + 2 * (parameters i).Cmu

theorem parameters_checked (i : Fin 20) : (parameters i).check=true := by
  fin_cases i
  · exact Stage80ConstantData.Case23.parameters_checked
  · exact Stage80ConstantData.Case24.parameters_checked
  · exact Stage80ConstantData.Case25.parameters_checked
  · exact Stage80ConstantData.Case26.parameters_checked
  · exact Stage80ConstantData.Case27.parameters_checked
  · exact Stage80ConstantData.Case28.parameters_checked
  · exact Stage80ConstantData.Case29.parameters_checked
  · exact Stage80ConstantData.Case30.parameters_checked
  · exact Stage80ConstantData.Case31.parameters_checked
  · exact Stage80ConstantData.Case32.parameters_checked
  · exact Stage80ConstantData.Case33.parameters_checked
  · exact Stage80ConstantData.Case34.parameters_checked
  · exact Stage80ConstantData.Case35.parameters_checked
  · exact Stage80ConstantData.Case36.parameters_checked
  · exact Stage80ConstantData.Case37.parameters_checked
  · exact Stage80ConstantData.Case38.parameters_checked
  · exact Stage80ConstantData.Case39.parameters_checked
  · exact Stage80ConstantData.Case40.parameters_checked
  · exact Stage80ConstantData.Case41.parameters_checked
  · exact Stage80ConstantData.Case42.parameters_checked

theorem domain_checked (i : Fin 20) : (domain i).check=true := by
  fin_cases i
  · exact Stage80ConstantData.Case23.domain_checked
  · exact Stage80ConstantData.Case24.domain_checked
  · exact Stage80ConstantData.Case25.domain_checked
  · exact Stage80ConstantData.Case26.domain_checked
  · exact Stage80ConstantData.Case27.domain_checked
  · exact Stage80ConstantData.Case28.domain_checked
  · exact Stage80ConstantData.Case29.domain_checked
  · exact Stage80ConstantData.Case30.domain_checked
  · exact Stage80ConstantData.Case31.domain_checked
  · exact Stage80ConstantData.Case32.domain_checked
  · exact Stage80ConstantData.Case33.domain_checked
  · exact Stage80ConstantData.Case34.domain_checked
  · exact Stage80ConstantData.Case35.domain_checked
  · exact Stage80ConstantData.Case36.domain_checked
  · exact Stage80ConstantData.Case37.domain_checked
  · exact Stage80ConstantData.Case38.domain_checked
  · exact Stage80ConstantData.Case39.domain_checked
  · exact Stage80ConstantData.Case40.domain_checked
  · exact Stage80ConstantData.Case41.domain_checked
  · exact Stage80ConstantData.Case42.domain_checked

theorem source_valid (i : Fin 20) : MessageSourceRowValid (ExactSelectionSource.toMessage (parameters i)) (domain i).lower (domain i).b := by
  fin_cases i
  · exact Stage80ConstantData.Case23.source_valid
  · exact Stage80ConstantData.Case24.source_valid
  · exact Stage80ConstantData.Case25.source_valid
  · exact Stage80ConstantData.Case26.source_valid
  · exact Stage80ConstantData.Case27.source_valid
  · exact Stage80ConstantData.Case28.source_valid
  · exact Stage80ConstantData.Case29.source_valid
  · exact Stage80ConstantData.Case30.source_valid
  · exact Stage80ConstantData.Case31.source_valid
  · exact Stage80ConstantData.Case32.source_valid
  · exact Stage80ConstantData.Case33.source_valid
  · exact Stage80ConstantData.Case34.source_valid
  · exact Stage80ConstantData.Case35.source_valid
  · exact Stage80ConstantData.Case36.source_valid
  · exact Stage80ConstantData.Case37.source_valid
  · exact Stage80ConstantData.Case38.source_valid
  · exact Stage80ConstantData.Case39.source_valid
  · exact Stage80ConstantData.Case40.source_valid
  · exact Stage80ConstantData.Case41.source_valid
  · exact Stage80ConstantData.Case42.source_valid

variable {V : Type*} [DecidableEq V]

theorem actual_variance (i : Fin 20) (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) {z : ℝ}
    (hzlo : ((domain i).lower : ℝ) ≤ z) (hzhi : z ≤ ((domain i).b : ℝ)) :
    hardCoreVariance G S z ≤
      ((parameters i).CJ : ℝ) * hardCoreMarginalSelectionScore G S z (domain i).b +
      ((parameters i).Cmu : ℝ) * hardCoreMean G S z :=
  ExactSelectionSource.forest_variance (parameters i) (parameters_checked i) G hG S
    (ParametricSource.Domain.check_sound (domain_checked i)).lower_pos hzlo hzhi (source_valid i)

theorem actual_variance_le_mass (i : Fin 20) {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hzlo : ((domain i).lower : ℝ) ≤ z) (hzhi : z ≤ ((domain i).b : ℝ)) :
    hardCoreVariance G S z ≤ (factor i : ℝ) * hardCoreOccupiedMass G S B z := by
  have h := ExactSelectionSource.variance_le_mass (parameters i) (parameters_checked i) hB hG
    (ParametricSource.Domain.check_sound (domain_checked i)).lower_pos hzlo hzhi (source_valid i)
  simpa only [factor, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat] using h

#print axioms source_valid
#print axioms actual_variance
#print axioms actual_variance_le_mass
end ForestUnimodality.Stage80ConstantLibrary
