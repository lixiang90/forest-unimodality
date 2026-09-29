import ForestUnimodality.NonnegativeSourceData.Case01.Complete
import ForestUnimodality.NonnegativeSourceData.Case02.Complete
import ForestUnimodality.NonnegativeSourceData.Case03.Complete
import ForestUnimodality.NonnegativeSourceData.Case04.Complete
import ForestUnimodality.NonnegativeSourceData.Case05.Complete
import ForestUnimodality.NonnegativeSourceData.Case06.Complete
import ForestUnimodality.NonnegativeSourceData.Case07.Complete
import ForestUnimodality.NonnegativeSourceData.Case08.Complete
import ForestUnimodality.NonnegativeSourceData.Case09.Complete
import ForestUnimodality.NonnegativeSourceData.Case10.Complete
import ForestUnimodality.NonnegativeSourceData.Case11.Complete
import ForestUnimodality.NonnegativeSourceData.Case12.Complete
import ForestUnimodality.NonnegativeSourceData.Case13.Complete
import ForestUnimodality.NonnegativeSourceData.Case14.Complete
import ForestUnimodality.NonnegativeSourceData.Case15.Complete
import ForestUnimodality.NonnegativeSourceData.Case16.Complete
import ForestUnimodality.ConstantSourceLaplace
namespace ForestUnimodality.NonnegativeSourceLibrary
def parameters : Fin 16→NonnegativeSource.Parameters := ![NonnegativeSourceData.Case01.parameters, NonnegativeSourceData.Case02.parameters, NonnegativeSourceData.Case03.parameters, NonnegativeSourceData.Case04.parameters, NonnegativeSourceData.Case05.parameters, NonnegativeSourceData.Case06.parameters, NonnegativeSourceData.Case07.parameters, NonnegativeSourceData.Case08.parameters, NonnegativeSourceData.Case09.parameters, NonnegativeSourceData.Case10.parameters, NonnegativeSourceData.Case11.parameters, NonnegativeSourceData.Case12.parameters, NonnegativeSourceData.Case13.parameters, NonnegativeSourceData.Case14.parameters, NonnegativeSourceData.Case15.parameters, NonnegativeSourceData.Case16.parameters]
theorem parameters_checked (i : Fin 16) : (parameters i).check=true := by
  fin_cases i
  · exact NonnegativeSourceData.Case01.parameters_checked
  · exact NonnegativeSourceData.Case02.parameters_checked
  · exact NonnegativeSourceData.Case03.parameters_checked
  · exact NonnegativeSourceData.Case04.parameters_checked
  · exact NonnegativeSourceData.Case05.parameters_checked
  · exact NonnegativeSourceData.Case06.parameters_checked
  · exact NonnegativeSourceData.Case07.parameters_checked
  · exact NonnegativeSourceData.Case08.parameters_checked
  · exact NonnegativeSourceData.Case09.parameters_checked
  · exact NonnegativeSourceData.Case10.parameters_checked
  · exact NonnegativeSourceData.Case11.parameters_checked
  · exact NonnegativeSourceData.Case12.parameters_checked
  · exact NonnegativeSourceData.Case13.parameters_checked
  · exact NonnegativeSourceData.Case14.parameters_checked
  · exact NonnegativeSourceData.Case15.parameters_checked
  · exact NonnegativeSourceData.Case16.parameters_checked
theorem source_valid (i : Fin 16) : NonnegativeSourceRowValid (parameters i).b (parameters i).A (parameters i).u (parameters i).v := by
  fin_cases i
  · exact NonnegativeSourceData.Case01.source_valid
  · exact NonnegativeSourceData.Case02.source_valid
  · exact NonnegativeSourceData.Case03.source_valid
  · exact NonnegativeSourceData.Case04.source_valid
  · exact NonnegativeSourceData.Case05.source_valid
  · exact NonnegativeSourceData.Case06.source_valid
  · exact NonnegativeSourceData.Case07.source_valid
  · exact NonnegativeSourceData.Case08.source_valid
  · exact NonnegativeSourceData.Case09.source_valid
  · exact NonnegativeSourceData.Case10.source_valid
  · exact NonnegativeSourceData.Case11.source_valid
  · exact NonnegativeSourceData.Case12.source_valid
  · exact NonnegativeSourceData.Case13.source_valid
  · exact NonnegativeSourceData.Case14.source_valid
  · exact NonnegativeSourceData.Case15.source_valid
  · exact NonnegativeSourceData.Case16.source_valid
variable {V : Type*} [DecidableEq V]
theorem actual_variance (i : Fin 16) (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S T : Finset V) (hTS : T⊆S) (activity : V→ℝ)
    (hactivity : ∀x∈S, 0≤activity x ∧ activity x≤((parameters i).b:ℝ)) :
    heterogeneousVariance G S activity (fun J=>((J∩T).card:ℝ))≤
      ((parameters i).A:ℝ)*(T.card:ℝ) := by
  have hp := NonnegativeSource.Parameters.check_sound (parameters_checked i)
  exact forest_independent_constant_source_variance G hG S T hTS activity
    hp.b_pos hactivity hp.u_nonneg hp.v_nonneg (source_valid i)

#print axioms actual_variance
end ForestUnimodality.NonnegativeSourceLibrary
