import ForestUnimodality.Stage900CurvatureData.Case06
import ForestUnimodality.Stage900CurvatureData.Case07
import ForestUnimodality.Stage900CurvatureData.Case08
import ForestUnimodality.Stage900CurvatureData.Case09
import ForestUnimodality.Stage900CurvatureData.Case10
import ForestUnimodality.Stage900CurvatureData.Case11
import ForestUnimodality.Stage900CurvatureData.Case12
import ForestUnimodality.Stage900CurvatureData.Case13
import ForestUnimodality.Stage900CurvatureData.Case14
import ForestUnimodality.Stage900CurvatureData.Case15
import ForestUnimodality.Stage900CurvatureData.Case16
import ForestUnimodality.Stage900CurvatureData.Case17
import ForestUnimodality.Stage900CurvatureData.Case18
import ForestUnimodality.Stage900CurvatureData.Case19
import ForestUnimodality.Stage900CurvatureData.Case20
import ForestUnimodality.Stage900CurvatureData.Case21
import ForestUnimodality.Stage900CurvatureData.Case22

namespace ForestUnimodality.Stage900CurvatureTable
open CurvatureBudget Set

noncomputable def row (i : Fin 17) : Parameters := ![Stage900CurvatureData.Case06.parameters, Stage900CurvatureData.Case07.parameters, Stage900CurvatureData.Case08.parameters, Stage900CurvatureData.Case09.parameters, Stage900CurvatureData.Case10.parameters, Stage900CurvatureData.Case11.parameters, Stage900CurvatureData.Case12.parameters, Stage900CurvatureData.Case13.parameters, Stage900CurvatureData.Case14.parameters, Stage900CurvatureData.Case15.parameters, Stage900CurvatureData.Case16.parameters, Stage900CurvatureData.Case17.parameters, Stage900CurvatureData.Case18.parameters, Stage900CurvatureData.Case19.parameters, Stage900CurvatureData.Case20.parameters, Stage900CurvatureData.Case21.parameters, Stage900CurvatureData.Case22.parameters] i

def sourceIndex (i : Fin 17) : Fin 28 := ⟨i.val+5,by omega⟩

theorem row_valid (i : Fin 17) : (row i).Valid := by
  fin_cases i
  · exact Stage900CurvatureData.Case06.parameters_valid
  · exact Stage900CurvatureData.Case07.parameters_valid
  · exact Stage900CurvatureData.Case08.parameters_valid
  · exact Stage900CurvatureData.Case09.parameters_valid
  · exact Stage900CurvatureData.Case10.parameters_valid
  · exact Stage900CurvatureData.Case11.parameters_valid
  · exact Stage900CurvatureData.Case12.parameters_valid
  · exact Stage900CurvatureData.Case13.parameters_valid
  · exact Stage900CurvatureData.Case14.parameters_valid
  · exact Stage900CurvatureData.Case15.parameters_valid
  · exact Stage900CurvatureData.Case16.parameters_valid
  · exact Stage900CurvatureData.Case17.parameters_valid
  · exact Stage900CurvatureData.Case18.parameters_valid
  · exact Stage900CurvatureData.Case19.parameters_valid
  · exact Stage900CurvatureData.Case20.parameters_valid
  · exact Stage900CurvatureData.Case21.parameters_valid
  · exact Stage900CurvatureData.Case22.parameters_valid

theorem margin_positive (i : Fin 17) : 0<budget (row i) (row i).start := by
  fin_cases i
  · exact Stage900CurvatureData.Case06.margin_positive
  · exact Stage900CurvatureData.Case07.margin_positive
  · exact Stage900CurvatureData.Case08.margin_positive
  · exact Stage900CurvatureData.Case09.margin_positive
  · exact Stage900CurvatureData.Case10.margin_positive
  · exact Stage900CurvatureData.Case11.margin_positive
  · exact Stage900CurvatureData.Case12.margin_positive
  · exact Stage900CurvatureData.Case13.margin_positive
  · exact Stage900CurvatureData.Case14.margin_positive
  · exact Stage900CurvatureData.Case15.margin_positive
  · exact Stage900CurvatureData.Case16.margin_positive
  · exact Stage900CurvatureData.Case17.margin_positive
  · exact Stage900CurvatureData.Case18.margin_positive
  · exact Stage900CurvatureData.Case19.margin_positive
  · exact Stage900CurvatureData.Case20.margin_positive
  · exact Stage900CurvatureData.Case21.margin_positive
  · exact Stage900CurvatureData.Case22.margin_positive

theorem covers {z : ℝ} (hlo : (22/25:ℝ)≤z) (hhi : z≤(57/50:ℝ)) :
    ∃i : Fin 17,(row i).a≤z ∧ z≤(row i).b := by
  by_cases h0 : z≤(9/10:ℝ)
  · refine ⟨0,?_⟩
    change (22/25:ℝ)≤z ∧ z≤(9/10:ℝ)
    constructor <;> linarith
  by_cases h1 : z≤(23/25:ℝ)
  · refine ⟨1,?_⟩
    change (9/10:ℝ)≤z ∧ z≤(23/25:ℝ)
    constructor <;> linarith
  by_cases h2 : z≤(47/50:ℝ)
  · refine ⟨2,?_⟩
    change (23/25:ℝ)≤z ∧ z≤(47/50:ℝ)
    constructor <;> linarith
  by_cases h3 : z≤(24/25:ℝ)
  · refine ⟨3,?_⟩
    change (47/50:ℝ)≤z ∧ z≤(24/25:ℝ)
    constructor <;> linarith
  by_cases h4 : z≤(49/50:ℝ)
  · refine ⟨4,?_⟩
    change (24/25:ℝ)≤z ∧ z≤(49/50:ℝ)
    constructor <;> linarith
  by_cases h5 : z≤(1:ℝ)
  · refine ⟨5,?_⟩
    change (49/50:ℝ)≤z ∧ z≤(1:ℝ)
    constructor <;> linarith
  by_cases h6 : z≤(51/50:ℝ)
  · refine ⟨6,?_⟩
    change (1:ℝ)≤z ∧ z≤(51/50:ℝ)
    constructor <;> linarith
  by_cases h7 : z≤(26/25:ℝ)
  · refine ⟨7,?_⟩
    change (51/50:ℝ)≤z ∧ z≤(26/25:ℝ)
    constructor <;> linarith
  by_cases h8 : z≤(53/50:ℝ)
  · refine ⟨8,?_⟩
    change (26/25:ℝ)≤z ∧ z≤(53/50:ℝ)
    constructor <;> linarith
  by_cases h9 : z≤(107/100:ℝ)
  · refine ⟨9,?_⟩
    change (53/50:ℝ)≤z ∧ z≤(107/100:ℝ)
    constructor <;> linarith
  by_cases h10 : z≤(27/25:ℝ)
  · refine ⟨10,?_⟩
    change (107/100:ℝ)≤z ∧ z≤(27/25:ℝ)
    constructor <;> linarith
  by_cases h11 : z≤(109/100:ℝ)
  · refine ⟨11,?_⟩
    change (27/25:ℝ)≤z ∧ z≤(109/100:ℝ)
    constructor <;> linarith
  by_cases h12 : z≤(11/10:ℝ)
  · refine ⟨12,?_⟩
    change (109/100:ℝ)≤z ∧ z≤(11/10:ℝ)
    constructor <;> linarith
  by_cases h13 : z≤(111/100:ℝ)
  · refine ⟨13,?_⟩
    change (11/10:ℝ)≤z ∧ z≤(111/100:ℝ)
    constructor <;> linarith
  by_cases h14 : z≤(28/25:ℝ)
  · refine ⟨14,?_⟩
    change (111/100:ℝ)≤z ∧ z≤(28/25:ℝ)
    constructor <;> linarith
  by_cases h15 : z≤(113/100:ℝ)
  · refine ⟨15,?_⟩
    change (28/25:ℝ)≤z ∧ z≤(113/100:ℝ)
    constructor <;> linarith
  refine ⟨16,?_⟩
  change (113/100:ℝ)≤z ∧ z≤(57/50:ℝ)
  constructor <;> linarith

#print axioms row_valid
#print axioms margin_positive
#print axioms covers
end ForestUnimodality.Stage900CurvatureTable
