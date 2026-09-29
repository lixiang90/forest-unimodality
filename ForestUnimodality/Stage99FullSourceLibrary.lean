import ForestUnimodality.Stage99FullSourceData.Case01.Complete
import ForestUnimodality.Stage99FullSourceData.Case02.Complete
import ForestUnimodality.Stage99FullSourceData.Case03.Complete
import ForestUnimodality.FixedIndependentFlow
namespace ForestUnimodality.Stage99FullSourceLibrary
open Set
def parameters : Fin 3→RationalSourceParameters := ![Stage99FullSourceData.Case01.parameters, Stage99FullSourceData.Case02.parameters, Stage99FullSourceData.Case03.parameters]
def domain : Fin 3→ParametricSource.Domain := ![Stage99FullSourceData.Case01.domain, Stage99FullSourceData.Case02.domain, Stage99FullSourceData.Case03.domain]
theorem parameters_checked (i : Fin 3) : (parameters i).admissibleCheck=true := by
  fin_cases i <;> first
  | exact Stage99FullSourceData.Case01.parameters_checked
  | exact Stage99FullSourceData.Case02.parameters_checked
  | exact Stage99FullSourceData.Case03.parameters_checked
theorem domain_checked (i : Fin 3) : (domain i).check=true := by
  fin_cases i <;> first
  | exact Stage99FullSourceData.Case01.domain_checked
  | exact Stage99FullSourceData.Case02.domain_checked
  | exact Stage99FullSourceData.Case03.domain_checked
theorem source_valid (i : Fin 3) : FullSourceRowValid (parameters i).toReal (domain i).lower (domain i).b := by
  fin_cases i <;> first
  | exact Stage99FullSourceData.Case01.source_valid
  | exact Stage99FullSourceData.Case02.source_valid
  | exact Stage99FullSourceData.Case03.source_valid
theorem coefficient_nonneg (i : Fin 3) : 0≤((parameters i).A:ℝ)+(parameters i).C := by
  fin_cases i <;> norm_num [parameters,Stage99FullSourceData.Case01.parameters,
    Stage99FullSourceData.Case02.parameters,Stage99FullSourceData.Case03.parameters]
variable {V : Type*} [DecidableEq V]
theorem actual_variance (i : Fin 3) (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (activity : V→ℝ)
    (hactivity : ∀x∈S, ((domain i).lower:ℝ)≤activity x ∧ activity x≤((domain i).b:ℝ)) :
    heterogeneousVariance G S activity (fun J=>(J.card:ℝ)) ≤
      (((parameters i).A:ℝ)+(parameters i).C)*heterogeneousMean G S activity (fun J=>(J.card:ℝ)) :=
  forest_full_count_variance_of_scalar_certificate G hG S activity
    (ParametricSource.Domain.check_sound (domain_checked i)).lower_pos hactivity (parameters i).toReal
    ((parameters i).admissible_sound (parameters_checked i)) (source_valid i)
/-- The full-count source controls the same fixed-B heterogeneous tilt. -/
theorem variance_on_step (i : Fin 3) (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S B : Finset V) {z a b start finish m U : ℝ}
    (ha : 0<a) (hzlo : a≤z) (hzhi : z≤b) (hstart : 0≤start)
    (hlo : ((domain i).lower:ℝ)≤a*Real.exp (-finish)) (hhi : b≤((domain i).b:ℝ))
    (hmu : ∀t∈Icc start finish, FixedIndependentTilt.totalMean G S B z t≤m*U) :
    ∀t∈Icc start finish,
      FiniteTilt.variance (independentSubsets G S)
        (FixedIndependentTilt.weight B z (z*Real.exp (-t))) (fun J=>(J.card:ℝ)) ≤
      m*((((parameters i).A:ℝ)+(parameters i).C)*U) := by
  intro t ht
  have hh := actual_variance i G hG S (independentTiltActivities B z (Real.exp (-t)))
    (fun v _=>FixedIndependentTilt.closed_step_activities B ha hzlo hzhi hstart hlo hhi t ht v)
  have hb := mul_le_mul_of_nonneg_left (hmu t ht) (coefficient_nonneg i)
  simp only [heterogeneousVariance,heterogeneousMean,
    ←FixedIndependentTilt.weight_eq_heterogeneous,FixedIndependentTilt.totalMean] at hh hb
  nlinarith
#print axioms variance_on_step
#print axioms actual_variance
end ForestUnimodality.Stage99FullSourceLibrary
