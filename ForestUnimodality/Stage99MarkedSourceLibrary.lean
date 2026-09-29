import ForestUnimodality.Stage99MarkedSourceData.Case01.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case02.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case03.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case04.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case05.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case06.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case07.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case08.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case09.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case10.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case11.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case12.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case13.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case14.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case15.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case16.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case17.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case18.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case19.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case20.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case21.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case22.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case23.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case24.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case25.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case26.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case27.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case28.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case29.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case30.Complete
import ForestUnimodality.Stage99MarkedSourceData.Case31.Complete
import ForestUnimodality.FixedIndependentFlow
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.Stage99MarkedSourceLibrary
open Set
def parameters : Fin 31→RationalSourceParameters := ![Stage99MarkedSourceData.Case01.parameters, Stage99MarkedSourceData.Case02.parameters, Stage99MarkedSourceData.Case03.parameters, Stage99MarkedSourceData.Case04.parameters, Stage99MarkedSourceData.Case05.parameters, Stage99MarkedSourceData.Case06.parameters, Stage99MarkedSourceData.Case07.parameters, Stage99MarkedSourceData.Case08.parameters, Stage99MarkedSourceData.Case09.parameters, Stage99MarkedSourceData.Case10.parameters, Stage99MarkedSourceData.Case11.parameters, Stage99MarkedSourceData.Case12.parameters, Stage99MarkedSourceData.Case13.parameters, Stage99MarkedSourceData.Case14.parameters, Stage99MarkedSourceData.Case15.parameters, Stage99MarkedSourceData.Case16.parameters, Stage99MarkedSourceData.Case17.parameters, Stage99MarkedSourceData.Case18.parameters, Stage99MarkedSourceData.Case19.parameters, Stage99MarkedSourceData.Case20.parameters, Stage99MarkedSourceData.Case21.parameters, Stage99MarkedSourceData.Case22.parameters, Stage99MarkedSourceData.Case23.parameters, Stage99MarkedSourceData.Case24.parameters, Stage99MarkedSourceData.Case25.parameters, Stage99MarkedSourceData.Case26.parameters, Stage99MarkedSourceData.Case27.parameters, Stage99MarkedSourceData.Case28.parameters, Stage99MarkedSourceData.Case29.parameters, Stage99MarkedSourceData.Case30.parameters, Stage99MarkedSourceData.Case31.parameters]
def domain : Fin 31→ParametricSource.Domain := ![Stage99MarkedSourceData.Case01.domain, Stage99MarkedSourceData.Case02.domain, Stage99MarkedSourceData.Case03.domain, Stage99MarkedSourceData.Case04.domain, Stage99MarkedSourceData.Case05.domain, Stage99MarkedSourceData.Case06.domain, Stage99MarkedSourceData.Case07.domain, Stage99MarkedSourceData.Case08.domain, Stage99MarkedSourceData.Case09.domain, Stage99MarkedSourceData.Case10.domain, Stage99MarkedSourceData.Case11.domain, Stage99MarkedSourceData.Case12.domain, Stage99MarkedSourceData.Case13.domain, Stage99MarkedSourceData.Case14.domain, Stage99MarkedSourceData.Case15.domain, Stage99MarkedSourceData.Case16.domain, Stage99MarkedSourceData.Case17.domain, Stage99MarkedSourceData.Case18.domain, Stage99MarkedSourceData.Case19.domain, Stage99MarkedSourceData.Case20.domain, Stage99MarkedSourceData.Case21.domain, Stage99MarkedSourceData.Case22.domain, Stage99MarkedSourceData.Case23.domain, Stage99MarkedSourceData.Case24.domain, Stage99MarkedSourceData.Case25.domain, Stage99MarkedSourceData.Case26.domain, Stage99MarkedSourceData.Case27.domain, Stage99MarkedSourceData.Case28.domain, Stage99MarkedSourceData.Case29.domain, Stage99MarkedSourceData.Case30.domain, Stage99MarkedSourceData.Case31.domain]
theorem parameters_checked (i : Fin 31) : (parameters i).admissibleCheck=true := by
  fin_cases i <;> first
  | exact Stage99MarkedSourceData.Case01.parameters_checked
  | exact Stage99MarkedSourceData.Case02.parameters_checked
  | exact Stage99MarkedSourceData.Case03.parameters_checked
  | exact Stage99MarkedSourceData.Case04.parameters_checked
  | exact Stage99MarkedSourceData.Case05.parameters_checked
  | exact Stage99MarkedSourceData.Case06.parameters_checked
  | exact Stage99MarkedSourceData.Case07.parameters_checked
  | exact Stage99MarkedSourceData.Case08.parameters_checked
  | exact Stage99MarkedSourceData.Case09.parameters_checked
  | exact Stage99MarkedSourceData.Case10.parameters_checked
  | exact Stage99MarkedSourceData.Case11.parameters_checked
  | exact Stage99MarkedSourceData.Case12.parameters_checked
  | exact Stage99MarkedSourceData.Case13.parameters_checked
  | exact Stage99MarkedSourceData.Case14.parameters_checked
  | exact Stage99MarkedSourceData.Case15.parameters_checked
  | exact Stage99MarkedSourceData.Case16.parameters_checked
  | exact Stage99MarkedSourceData.Case17.parameters_checked
  | exact Stage99MarkedSourceData.Case18.parameters_checked
  | exact Stage99MarkedSourceData.Case19.parameters_checked
  | exact Stage99MarkedSourceData.Case20.parameters_checked
  | exact Stage99MarkedSourceData.Case21.parameters_checked
  | exact Stage99MarkedSourceData.Case22.parameters_checked
  | exact Stage99MarkedSourceData.Case23.parameters_checked
  | exact Stage99MarkedSourceData.Case24.parameters_checked
  | exact Stage99MarkedSourceData.Case25.parameters_checked
  | exact Stage99MarkedSourceData.Case26.parameters_checked
  | exact Stage99MarkedSourceData.Case27.parameters_checked
  | exact Stage99MarkedSourceData.Case28.parameters_checked
  | exact Stage99MarkedSourceData.Case29.parameters_checked
  | exact Stage99MarkedSourceData.Case30.parameters_checked
  | exact Stage99MarkedSourceData.Case31.parameters_checked
theorem domain_checked (i : Fin 31) : (domain i).check=true := by
  fin_cases i <;> first
  | exact Stage99MarkedSourceData.Case01.domain_checked
  | exact Stage99MarkedSourceData.Case02.domain_checked
  | exact Stage99MarkedSourceData.Case03.domain_checked
  | exact Stage99MarkedSourceData.Case04.domain_checked
  | exact Stage99MarkedSourceData.Case05.domain_checked
  | exact Stage99MarkedSourceData.Case06.domain_checked
  | exact Stage99MarkedSourceData.Case07.domain_checked
  | exact Stage99MarkedSourceData.Case08.domain_checked
  | exact Stage99MarkedSourceData.Case09.domain_checked
  | exact Stage99MarkedSourceData.Case10.domain_checked
  | exact Stage99MarkedSourceData.Case11.domain_checked
  | exact Stage99MarkedSourceData.Case12.domain_checked
  | exact Stage99MarkedSourceData.Case13.domain_checked
  | exact Stage99MarkedSourceData.Case14.domain_checked
  | exact Stage99MarkedSourceData.Case15.domain_checked
  | exact Stage99MarkedSourceData.Case16.domain_checked
  | exact Stage99MarkedSourceData.Case17.domain_checked
  | exact Stage99MarkedSourceData.Case18.domain_checked
  | exact Stage99MarkedSourceData.Case19.domain_checked
  | exact Stage99MarkedSourceData.Case20.domain_checked
  | exact Stage99MarkedSourceData.Case21.domain_checked
  | exact Stage99MarkedSourceData.Case22.domain_checked
  | exact Stage99MarkedSourceData.Case23.domain_checked
  | exact Stage99MarkedSourceData.Case24.domain_checked
  | exact Stage99MarkedSourceData.Case25.domain_checked
  | exact Stage99MarkedSourceData.Case26.domain_checked
  | exact Stage99MarkedSourceData.Case27.domain_checked
  | exact Stage99MarkedSourceData.Case28.domain_checked
  | exact Stage99MarkedSourceData.Case29.domain_checked
  | exact Stage99MarkedSourceData.Case30.domain_checked
  | exact Stage99MarkedSourceData.Case31.domain_checked
theorem source_valid (i : Fin 31) : SourceRowValid (parameters i).toReal (domain i).lower (domain i).b := by
  fin_cases i <;> first
  | exact Stage99MarkedSourceData.Case01.source_valid
  | exact Stage99MarkedSourceData.Case02.source_valid
  | exact Stage99MarkedSourceData.Case03.source_valid
  | exact Stage99MarkedSourceData.Case04.source_valid
  | exact Stage99MarkedSourceData.Case05.source_valid
  | exact Stage99MarkedSourceData.Case06.source_valid
  | exact Stage99MarkedSourceData.Case07.source_valid
  | exact Stage99MarkedSourceData.Case08.source_valid
  | exact Stage99MarkedSourceData.Case09.source_valid
  | exact Stage99MarkedSourceData.Case10.source_valid
  | exact Stage99MarkedSourceData.Case11.source_valid
  | exact Stage99MarkedSourceData.Case12.source_valid
  | exact Stage99MarkedSourceData.Case13.source_valid
  | exact Stage99MarkedSourceData.Case14.source_valid
  | exact Stage99MarkedSourceData.Case15.source_valid
  | exact Stage99MarkedSourceData.Case16.source_valid
  | exact Stage99MarkedSourceData.Case17.source_valid
  | exact Stage99MarkedSourceData.Case18.source_valid
  | exact Stage99MarkedSourceData.Case19.source_valid
  | exact Stage99MarkedSourceData.Case20.source_valid
  | exact Stage99MarkedSourceData.Case21.source_valid
  | exact Stage99MarkedSourceData.Case22.source_valid
  | exact Stage99MarkedSourceData.Case23.source_valid
  | exact Stage99MarkedSourceData.Case24.source_valid
  | exact Stage99MarkedSourceData.Case25.source_valid
  | exact Stage99MarkedSourceData.Case26.source_valid
  | exact Stage99MarkedSourceData.Case27.source_valid
  | exact Stage99MarkedSourceData.Case28.source_valid
  | exact Stage99MarkedSourceData.Case29.source_valid
  | exact Stage99MarkedSourceData.Case30.source_valid
  | exact Stage99MarkedSourceData.Case31.source_valid
theorem coefficients_nonneg (i : Fin 31) :
    0≤((parameters i).A:ℝ) ∧ 0≤((parameters i).C:ℝ) := by
  fin_cases i <;> norm_num [parameters,Stage99MarkedSourceData.Case01.parameters,
    Stage99MarkedSourceData.Case02.parameters,
    Stage99MarkedSourceData.Case03.parameters,
    Stage99MarkedSourceData.Case04.parameters,
    Stage99MarkedSourceData.Case05.parameters,
    Stage99MarkedSourceData.Case06.parameters,
    Stage99MarkedSourceData.Case07.parameters,
    Stage99MarkedSourceData.Case08.parameters,
    Stage99MarkedSourceData.Case09.parameters,
    Stage99MarkedSourceData.Case10.parameters,
    Stage99MarkedSourceData.Case11.parameters,
    Stage99MarkedSourceData.Case12.parameters,
    Stage99MarkedSourceData.Case13.parameters,
    Stage99MarkedSourceData.Case14.parameters,
    Stage99MarkedSourceData.Case15.parameters,
    Stage99MarkedSourceData.Case16.parameters,
    Stage99MarkedSourceData.Case17.parameters,
    Stage99MarkedSourceData.Case18.parameters,
    Stage99MarkedSourceData.Case19.parameters,
    Stage99MarkedSourceData.Case20.parameters,
    Stage99MarkedSourceData.Case21.parameters,
    Stage99MarkedSourceData.Case22.parameters,
    Stage99MarkedSourceData.Case23.parameters,
    Stage99MarkedSourceData.Case24.parameters,
    Stage99MarkedSourceData.Case25.parameters,
    Stage99MarkedSourceData.Case26.parameters,
    Stage99MarkedSourceData.Case27.parameters,
    Stage99MarkedSourceData.Case28.parameters,
    Stage99MarkedSourceData.Case29.parameters,
    Stage99MarkedSourceData.Case30.parameters,
    Stage99MarkedSourceData.Case31.parameters]
variable {V : Type*} [DecidableEq V]
theorem actual_variance (i : Fin 31) (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S B : Finset V) (hB : G.IsIndepSet (B:Set V)) (activity : V→ℝ)
    (hactivity : ∀x∈S, ((domain i).lower:ℝ)≤activity x ∧ activity x≤((domain i).b:ℝ)) :
    heterogeneousVariance G S activity (fun J=>((J∩B).card:ℝ)) ≤
      ((parameters i).A:ℝ)*heterogeneousMean G S activity (fun J=>(J.card:ℝ))+
      ((parameters i).C:ℝ)*heterogeneousMean G S activity (fun J=>((J∩B).card:ℝ)) :=
  forest_independent_count_variance_of_scalar_certificate G hG S B hB activity
    (ParametricSource.Domain.check_sound (domain_checked i)).lower_pos hactivity (parameters i).toReal
    ((parameters i).admissible_sound (parameters_checked i)) (source_valid i)
/-- Every source use covers the complete closed step of the same actual tilt. -/
theorem variance_on_step (i : Fin 31) (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S B : Finset V) (hB : G.IsIndepSet (B:Set V)) {z a b start finish m U : ℝ}
    (ha : 0<a) (hzlo : a≤z) (hzhi : z≤b) (hstart : 0≤start)
    (hlo : ((domain i).lower:ℝ)≤a*Real.exp (-finish)) (hhi : b≤((domain i).b:ℝ))
    (hmu : ∀t∈Icc start finish, FixedIndependentTilt.totalMean G S B z t≤m*U) :
    ∀t∈Icc start finish, FixedIndependentTilt.markedVariance G S B z t≤
      m*(((parameters i).A:ℝ)*U)+((parameters i).C:ℝ)*FixedIndependentTilt.markedMean G S B z t :=
  FixedIndependentTilt.marked_source_on_step G hG S B hB ha hzlo hzhi hstart
    (ParametricSource.Domain.check_sound (domain_checked i)).lower_pos hlo hhi
    (parameters i).toReal ((parameters i).admissible_sound (parameters_checked i))
    (coefficients_nonneg i).1 (source_valid i) hmu
#print axioms variance_on_step
#print axioms actual_variance
end ForestUnimodality.Stage99MarkedSourceLibrary
