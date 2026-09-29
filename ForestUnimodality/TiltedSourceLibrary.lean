import ForestUnimodality.TiltedSourceData.Case01.Actual
import ForestUnimodality.TiltedSourceData.Case02.Actual
import ForestUnimodality.TiltedSourceData.Case03.Actual
import ForestUnimodality.TiltedSourceData.Case04.Actual
import ForestUnimodality.TiltedSourceData.Case05.Actual
import ForestUnimodality.TiltedSourceData.Case06.Actual
import ForestUnimodality.TiltedSourceData.Case07.Actual
import ForestUnimodality.TiltedSourceData.Case08.Actual
import ForestUnimodality.TiltedSourceData.Case09.Actual
import ForestUnimodality.TiltedSourceData.Case10.Actual
import ForestUnimodality.TiltedSourceData.Case11.Actual
import ForestUnimodality.TiltedSourceData.Case12.Actual
import ForestUnimodality.TiltedSourceData.Case13.Actual
import ForestUnimodality.TiltedSourceData.Case14.Actual
import ForestUnimodality.TiltedSourceData.Case15.Actual
import ForestUnimodality.TiltedSourceData.Case16.Actual
import ForestUnimodality.TiltedSourceData.Case17.Actual
import ForestUnimodality.TiltedSourceData.Case18.Actual
import ForestUnimodality.TiltedSourceData.Case19.Actual
import ForestUnimodality.TiltedSourceData.Case20.Actual
import ForestUnimodality.TiltedSourceData.Case21.Actual
import ForestUnimodality.TiltedSourceData.Case22.Actual
import ForestUnimodality.TiltedSourceData.Case23.Actual
import ForestUnimodality.TiltedSourceData.Case24.Actual
import ForestUnimodality.TiltedSourceData.Case25.Actual
import ForestUnimodality.TiltedSourceData.Case26.Actual
import ForestUnimodality.TiltedSourceData.Case27.Actual
import ForestUnimodality.TiltedSourceData.Case28.Actual
import ForestUnimodality.TiltedSourceData.Case29.Actual
import ForestUnimodality.TiltedSourceData.Case30.Actual
import ForestUnimodality.TiltedSourceData.Case31.Actual
import ForestUnimodality.TiltedSourceData.Case32.Actual
import ForestUnimodality.TiltedSourceData.Case33.Actual
import ForestUnimodality.TiltedSourceData.Case34.Actual
import ForestUnimodality.TiltedSourceData.Case35.Actual
import ForestUnimodality.TiltedSourceData.Case36.Actual

namespace ForestUnimodality.TiltedSourceLibrary
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def parameters : Fin 36→TiltedSource.Parameters := ![TiltedSourceData.Case01.parameters, TiltedSourceData.Case02.parameters, TiltedSourceData.Case03.parameters, TiltedSourceData.Case04.parameters, TiltedSourceData.Case05.parameters, TiltedSourceData.Case06.parameters, TiltedSourceData.Case07.parameters, TiltedSourceData.Case08.parameters, TiltedSourceData.Case09.parameters, TiltedSourceData.Case10.parameters, TiltedSourceData.Case11.parameters, TiltedSourceData.Case12.parameters, TiltedSourceData.Case13.parameters, TiltedSourceData.Case14.parameters, TiltedSourceData.Case15.parameters, TiltedSourceData.Case16.parameters, TiltedSourceData.Case17.parameters, TiltedSourceData.Case18.parameters, TiltedSourceData.Case19.parameters, TiltedSourceData.Case20.parameters, TiltedSourceData.Case21.parameters, TiltedSourceData.Case22.parameters, TiltedSourceData.Case23.parameters, TiltedSourceData.Case24.parameters, TiltedSourceData.Case25.parameters, TiltedSourceData.Case26.parameters, TiltedSourceData.Case27.parameters, TiltedSourceData.Case28.parameters, TiltedSourceData.Case29.parameters, TiltedSourceData.Case30.parameters, TiltedSourceData.Case31.parameters, TiltedSourceData.Case32.parameters, TiltedSourceData.Case33.parameters, TiltedSourceData.Case34.parameters, TiltedSourceData.Case35.parameters, TiltedSourceData.Case36.parameters]
def domain0 : Fin 36→SelectionSource.Domain := ![TiltedSourceData.Case01.domain0, TiltedSourceData.Case02.domain0, TiltedSourceData.Case03.domain0, TiltedSourceData.Case04.domain0, TiltedSourceData.Case05.domain0, TiltedSourceData.Case06.domain0, TiltedSourceData.Case07.domain0, TiltedSourceData.Case08.domain0, TiltedSourceData.Case09.domain0, TiltedSourceData.Case10.domain0, TiltedSourceData.Case11.domain0, TiltedSourceData.Case12.domain0, TiltedSourceData.Case13.domain0, TiltedSourceData.Case14.domain0, TiltedSourceData.Case15.domain0, TiltedSourceData.Case16.domain0, TiltedSourceData.Case17.domain0, TiltedSourceData.Case18.domain0, TiltedSourceData.Case19.domain0, TiltedSourceData.Case20.domain0, TiltedSourceData.Case21.domain0, TiltedSourceData.Case22.domain0, TiltedSourceData.Case23.domain0, TiltedSourceData.Case24.domain0, TiltedSourceData.Case25.domain0, TiltedSourceData.Case26.domain0, TiltedSourceData.Case27.domain0, TiltedSourceData.Case28.domain0, TiltedSourceData.Case29.domain0, TiltedSourceData.Case30.domain0, TiltedSourceData.Case31.domain0, TiltedSourceData.Case32.domain0, TiltedSourceData.Case33.domain0, TiltedSourceData.Case34.domain0, TiltedSourceData.Case35.domain0, TiltedSourceData.Case36.domain0]
def domain1 : Fin 36→SelectionSource.Domain := ![TiltedSourceData.Case01.domain1, TiltedSourceData.Case02.domain1, TiltedSourceData.Case03.domain1, TiltedSourceData.Case04.domain1, TiltedSourceData.Case05.domain1, TiltedSourceData.Case06.domain1, TiltedSourceData.Case07.domain1, TiltedSourceData.Case08.domain1, TiltedSourceData.Case09.domain1, TiltedSourceData.Case10.domain1, TiltedSourceData.Case11.domain1, TiltedSourceData.Case12.domain1, TiltedSourceData.Case13.domain1, TiltedSourceData.Case14.domain1, TiltedSourceData.Case15.domain1, TiltedSourceData.Case16.domain1, TiltedSourceData.Case17.domain1, TiltedSourceData.Case18.domain1, TiltedSourceData.Case19.domain1, TiltedSourceData.Case20.domain1, TiltedSourceData.Case21.domain1, TiltedSourceData.Case22.domain1, TiltedSourceData.Case23.domain1, TiltedSourceData.Case24.domain1, TiltedSourceData.Case25.domain1, TiltedSourceData.Case26.domain1, TiltedSourceData.Case27.domain1, TiltedSourceData.Case28.domain1, TiltedSourceData.Case29.domain1, TiltedSourceData.Case30.domain1, TiltedSourceData.Case31.domain1, TiltedSourceData.Case32.domain1, TiltedSourceData.Case33.domain1, TiltedSourceData.Case34.domain1, TiltedSourceData.Case35.domain1, TiltedSourceData.Case36.domain1]
theorem parameters_checked (i : Fin 36) : (parameters i).check=true := by
  fin_cases i
  · exact TiltedSourceData.Case01.parameters_checked
  · exact TiltedSourceData.Case02.parameters_checked
  · exact TiltedSourceData.Case03.parameters_checked
  · exact TiltedSourceData.Case04.parameters_checked
  · exact TiltedSourceData.Case05.parameters_checked
  · exact TiltedSourceData.Case06.parameters_checked
  · exact TiltedSourceData.Case07.parameters_checked
  · exact TiltedSourceData.Case08.parameters_checked
  · exact TiltedSourceData.Case09.parameters_checked
  · exact TiltedSourceData.Case10.parameters_checked
  · exact TiltedSourceData.Case11.parameters_checked
  · exact TiltedSourceData.Case12.parameters_checked
  · exact TiltedSourceData.Case13.parameters_checked
  · exact TiltedSourceData.Case14.parameters_checked
  · exact TiltedSourceData.Case15.parameters_checked
  · exact TiltedSourceData.Case16.parameters_checked
  · exact TiltedSourceData.Case17.parameters_checked
  · exact TiltedSourceData.Case18.parameters_checked
  · exact TiltedSourceData.Case19.parameters_checked
  · exact TiltedSourceData.Case20.parameters_checked
  · exact TiltedSourceData.Case21.parameters_checked
  · exact TiltedSourceData.Case22.parameters_checked
  · exact TiltedSourceData.Case23.parameters_checked
  · exact TiltedSourceData.Case24.parameters_checked
  · exact TiltedSourceData.Case25.parameters_checked
  · exact TiltedSourceData.Case26.parameters_checked
  · exact TiltedSourceData.Case27.parameters_checked
  · exact TiltedSourceData.Case28.parameters_checked
  · exact TiltedSourceData.Case29.parameters_checked
  · exact TiltedSourceData.Case30.parameters_checked
  · exact TiltedSourceData.Case31.parameters_checked
  · exact TiltedSourceData.Case32.parameters_checked
  · exact TiltedSourceData.Case33.parameters_checked
  · exact TiltedSourceData.Case34.parameters_checked
  · exact TiltedSourceData.Case35.parameters_checked
  · exact TiltedSourceData.Case36.parameters_checked
theorem domain0_checked (i : Fin 36) : (domain0 i).check=true := by
  fin_cases i
  · exact TiltedSourceData.Case01.domain0_checked
  · exact TiltedSourceData.Case02.domain0_checked
  · exact TiltedSourceData.Case03.domain0_checked
  · exact TiltedSourceData.Case04.domain0_checked
  · exact TiltedSourceData.Case05.domain0_checked
  · exact TiltedSourceData.Case06.domain0_checked
  · exact TiltedSourceData.Case07.domain0_checked
  · exact TiltedSourceData.Case08.domain0_checked
  · exact TiltedSourceData.Case09.domain0_checked
  · exact TiltedSourceData.Case10.domain0_checked
  · exact TiltedSourceData.Case11.domain0_checked
  · exact TiltedSourceData.Case12.domain0_checked
  · exact TiltedSourceData.Case13.domain0_checked
  · exact TiltedSourceData.Case14.domain0_checked
  · exact TiltedSourceData.Case15.domain0_checked
  · exact TiltedSourceData.Case16.domain0_checked
  · exact TiltedSourceData.Case17.domain0_checked
  · exact TiltedSourceData.Case18.domain0_checked
  · exact TiltedSourceData.Case19.domain0_checked
  · exact TiltedSourceData.Case20.domain0_checked
  · exact TiltedSourceData.Case21.domain0_checked
  · exact TiltedSourceData.Case22.domain0_checked
  · exact TiltedSourceData.Case23.domain0_checked
  · exact TiltedSourceData.Case24.domain0_checked
  · exact TiltedSourceData.Case25.domain0_checked
  · exact TiltedSourceData.Case26.domain0_checked
  · exact TiltedSourceData.Case27.domain0_checked
  · exact TiltedSourceData.Case28.domain0_checked
  · exact TiltedSourceData.Case29.domain0_checked
  · exact TiltedSourceData.Case30.domain0_checked
  · exact TiltedSourceData.Case31.domain0_checked
  · exact TiltedSourceData.Case32.domain0_checked
  · exact TiltedSourceData.Case33.domain0_checked
  · exact TiltedSourceData.Case34.domain0_checked
  · exact TiltedSourceData.Case35.domain0_checked
  · exact TiltedSourceData.Case36.domain0_checked
theorem domain1_checked (i : Fin 36) : (domain1 i).check=true := by
  fin_cases i
  · exact TiltedSourceData.Case01.domain1_checked
  · exact TiltedSourceData.Case02.domain1_checked
  · exact TiltedSourceData.Case03.domain1_checked
  · exact TiltedSourceData.Case04.domain1_checked
  · exact TiltedSourceData.Case05.domain1_checked
  · exact TiltedSourceData.Case06.domain1_checked
  · exact TiltedSourceData.Case07.domain1_checked
  · exact TiltedSourceData.Case08.domain1_checked
  · exact TiltedSourceData.Case09.domain1_checked
  · exact TiltedSourceData.Case10.domain1_checked
  · exact TiltedSourceData.Case11.domain1_checked
  · exact TiltedSourceData.Case12.domain1_checked
  · exact TiltedSourceData.Case13.domain1_checked
  · exact TiltedSourceData.Case14.domain1_checked
  · exact TiltedSourceData.Case15.domain1_checked
  · exact TiltedSourceData.Case16.domain1_checked
  · exact TiltedSourceData.Case17.domain1_checked
  · exact TiltedSourceData.Case18.domain1_checked
  · exact TiltedSourceData.Case19.domain1_checked
  · exact TiltedSourceData.Case20.domain1_checked
  · exact TiltedSourceData.Case21.domain1_checked
  · exact TiltedSourceData.Case22.domain1_checked
  · exact TiltedSourceData.Case23.domain1_checked
  · exact TiltedSourceData.Case24.domain1_checked
  · exact TiltedSourceData.Case25.domain1_checked
  · exact TiltedSourceData.Case26.domain1_checked
  · exact TiltedSourceData.Case27.domain1_checked
  · exact TiltedSourceData.Case28.domain1_checked
  · exact TiltedSourceData.Case29.domain1_checked
  · exact TiltedSourceData.Case30.domain1_checked
  · exact TiltedSourceData.Case31.domain1_checked
  · exact TiltedSourceData.Case32.domain1_checked
  · exact TiltedSourceData.Case33.domain1_checked
  · exact TiltedSourceData.Case34.domain1_checked
  · exact TiltedSourceData.Case35.domain1_checked
  · exact TiltedSourceData.Case36.domain1_checked
theorem source_valid (i : Fin 36) :
    TiltedSourceRowValid (parameters i).toReal (tiltedMarkCap (domain0 i).b (domain1 i).b) := by
  fin_cases i
  · exact TiltedSourceData.Case01.source_valid
  · exact TiltedSourceData.Case02.source_valid
  · exact TiltedSourceData.Case03.source_valid
  · exact TiltedSourceData.Case04.source_valid
  · exact TiltedSourceData.Case05.source_valid
  · exact TiltedSourceData.Case06.source_valid
  · exact TiltedSourceData.Case07.source_valid
  · exact TiltedSourceData.Case08.source_valid
  · exact TiltedSourceData.Case09.source_valid
  · exact TiltedSourceData.Case10.source_valid
  · exact TiltedSourceData.Case11.source_valid
  · exact TiltedSourceData.Case12.source_valid
  · exact TiltedSourceData.Case13.source_valid
  · exact TiltedSourceData.Case14.source_valid
  · exact TiltedSourceData.Case15.source_valid
  · exact TiltedSourceData.Case16.source_valid
  · exact TiltedSourceData.Case17.source_valid
  · exact TiltedSourceData.Case18.source_valid
  · exact TiltedSourceData.Case19.source_valid
  · exact TiltedSourceData.Case20.source_valid
  · exact TiltedSourceData.Case21.source_valid
  · exact TiltedSourceData.Case22.source_valid
  · exact TiltedSourceData.Case23.source_valid
  · exact TiltedSourceData.Case24.source_valid
  · exact TiltedSourceData.Case25.source_valid
  · exact TiltedSourceData.Case26.source_valid
  · exact TiltedSourceData.Case27.source_valid
  · exact TiltedSourceData.Case28.source_valid
  · exact TiltedSourceData.Case29.source_valid
  · exact TiltedSourceData.Case30.source_valid
  · exact TiltedSourceData.Case31.source_valid
  · exact TiltedSourceData.Case32.source_valid
  · exact TiltedSourceData.Case33.source_valid
  · exact TiltedSourceData.Case34.source_valid
  · exact TiltedSourceData.Case35.source_valid
  · exact TiltedSourceData.Case36.source_valid

variable {V : Type*} [DecidableEq V]

theorem actual_variance (i : Fin 36) (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S B : Finset V) (hB : G.IsIndepSet (B:Set V)) {z start t : ℝ} (hz : 0<z)
    (hzcap : z≤((domain0 i).b:ℝ)) (hstart : z*Real.exp (-start)≤((domain1 i).b:ℝ))
    (ht : start≤t) : FixedIndependentTilt.markedVariance G S B z t≤
      ((parameters i).C:ℝ)*FixedIndependentTilt.markedMean G S B z t :=
  forest_fixed_independent_tilt_variance G hG S B hB hz
    (ParametricSource.Domain.check_sound (domain0_checked i)).b_pos
    (ParametricSource.Domain.check_sound (domain1_checked i)).b_pos hzcap hstart
    (parameters i).toReal (TiltedSource.Parameters.check_sound (parameters_checked i)).1
    (source_valid i) t ht

#print axioms source_valid
#print axioms actual_variance
end ForestUnimodality.TiltedSourceLibrary
