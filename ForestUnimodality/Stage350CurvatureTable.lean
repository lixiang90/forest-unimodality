import ForestUnimodality.Stage350CurvatureData.Case07
import ForestUnimodality.Stage350CurvatureData.Case08
import ForestUnimodality.Stage350CurvatureData.Case09
import ForestUnimodality.Stage350CurvatureData.Case10
import ForestUnimodality.Stage350CurvatureData.Case11
import ForestUnimodality.Stage350CurvatureData.Case12
import ForestUnimodality.Stage350CurvatureData.Case13
import ForestUnimodality.Stage350CurvatureData.Case14
import ForestUnimodality.Stage350CurvatureData.Case15
import ForestUnimodality.Stage350CurvatureData.Case16
import ForestUnimodality.Stage350CurvatureData.Case17
import ForestUnimodality.Stage350CurvatureData.Case18
import ForestUnimodality.Stage350CurvatureData.Case19
import ForestUnimodality.Stage350CurvatureData.Case20
import ForestUnimodality.Stage350CurvatureData.Case21
import ForestUnimodality.Stage350CurvatureData.Case22
import ForestUnimodality.Stage350CurvatureData.Case23

namespace ForestUnimodality.Stage350CurvatureTable
open Stage350CurvatureBudget Set

noncomputable def row (i : Fin 17) : Parameters := ![Stage350CurvatureData.Case07.parameters, Stage350CurvatureData.Case08.parameters, Stage350CurvatureData.Case09.parameters, Stage350CurvatureData.Case10.parameters, Stage350CurvatureData.Case11.parameters, Stage350CurvatureData.Case12.parameters, Stage350CurvatureData.Case13.parameters, Stage350CurvatureData.Case14.parameters, Stage350CurvatureData.Case15.parameters, Stage350CurvatureData.Case16.parameters, Stage350CurvatureData.Case17.parameters, Stage350CurvatureData.Case18.parameters, Stage350CurvatureData.Case19.parameters, Stage350CurvatureData.Case20.parameters, Stage350CurvatureData.Case21.parameters, Stage350CurvatureData.Case22.parameters, Stage350CurvatureData.Case23.parameters] i

def sourceIndex (i : Fin 17) : Fin 43 := ⟨i.val+6,by omega⟩

theorem row_valid (i : Fin 17) : (row i).Valid := by
  fin_cases i
  · exact Stage350CurvatureData.Case07.parameters_valid
  · exact Stage350CurvatureData.Case08.parameters_valid
  · exact Stage350CurvatureData.Case09.parameters_valid
  · exact Stage350CurvatureData.Case10.parameters_valid
  · exact Stage350CurvatureData.Case11.parameters_valid
  · exact Stage350CurvatureData.Case12.parameters_valid
  · exact Stage350CurvatureData.Case13.parameters_valid
  · exact Stage350CurvatureData.Case14.parameters_valid
  · exact Stage350CurvatureData.Case15.parameters_valid
  · exact Stage350CurvatureData.Case16.parameters_valid
  · exact Stage350CurvatureData.Case17.parameters_valid
  · exact Stage350CurvatureData.Case18.parameters_valid
  · exact Stage350CurvatureData.Case19.parameters_valid
  · exact Stage350CurvatureData.Case20.parameters_valid
  · exact Stage350CurvatureData.Case21.parameters_valid
  · exact Stage350CurvatureData.Case22.parameters_valid
  · exact Stage350CurvatureData.Case23.parameters_valid

theorem margin_positive (i : Fin 17) : 0<budget (row i) (row i).start := by
  fin_cases i
  · exact Stage350CurvatureData.Case07.margin_positive
  · exact Stage350CurvatureData.Case08.margin_positive
  · exact Stage350CurvatureData.Case09.margin_positive
  · exact Stage350CurvatureData.Case10.margin_positive
  · exact Stage350CurvatureData.Case11.margin_positive
  · exact Stage350CurvatureData.Case12.margin_positive
  · exact Stage350CurvatureData.Case13.margin_positive
  · exact Stage350CurvatureData.Case14.margin_positive
  · exact Stage350CurvatureData.Case15.margin_positive
  · exact Stage350CurvatureData.Case16.margin_positive
  · exact Stage350CurvatureData.Case17.margin_positive
  · exact Stage350CurvatureData.Case18.margin_positive
  · exact Stage350CurvatureData.Case19.margin_positive
  · exact Stage350CurvatureData.Case20.margin_positive
  · exact Stage350CurvatureData.Case21.margin_positive
  · exact Stage350CurvatureData.Case22.margin_positive
  · exact Stage350CurvatureData.Case23.margin_positive

theorem main_positive (i : Fin 17) : 0<main (row i) (row i).start := by
  fin_cases i
  · exact Stage350CurvatureData.Case07.main_positive
  · exact Stage350CurvatureData.Case08.main_positive
  · exact Stage350CurvatureData.Case09.main_positive
  · exact Stage350CurvatureData.Case10.main_positive
  · exact Stage350CurvatureData.Case11.main_positive
  · exact Stage350CurvatureData.Case12.main_positive
  · exact Stage350CurvatureData.Case13.main_positive
  · exact Stage350CurvatureData.Case14.main_positive
  · exact Stage350CurvatureData.Case15.main_positive
  · exact Stage350CurvatureData.Case16.main_positive
  · exact Stage350CurvatureData.Case17.main_positive
  · exact Stage350CurvatureData.Case18.main_positive
  · exact Stage350CurvatureData.Case19.main_positive
  · exact Stage350CurvatureData.Case20.main_positive
  · exact Stage350CurvatureData.Case21.main_positive
  · exact Stage350CurvatureData.Case22.main_positive
  · exact Stage350CurvatureData.Case23.main_positive

theorem bad_polynomial_nonpos (i : Fin 17) : let t:=((7/20:ℝ)*(row i).start+1/(6*(row i).vmin))/((row i).start+1/(6*(row i).vmin))
    Real.exp (-(9/20:ℝ))*(209/200+(159/200)*(t-1))-B (row i).largeBeta*(t-1)^2≤0 := by
  fin_cases i
  · exact Stage350CurvatureData.Case07.bad_polynomial_nonpos
  · exact Stage350CurvatureData.Case08.bad_polynomial_nonpos
  · exact Stage350CurvatureData.Case09.bad_polynomial_nonpos
  · exact Stage350CurvatureData.Case10.bad_polynomial_nonpos
  · exact Stage350CurvatureData.Case11.bad_polynomial_nonpos
  · exact Stage350CurvatureData.Case12.bad_polynomial_nonpos
  · exact Stage350CurvatureData.Case13.bad_polynomial_nonpos
  · exact Stage350CurvatureData.Case14.bad_polynomial_nonpos
  · exact Stage350CurvatureData.Case15.bad_polynomial_nonpos
  · exact Stage350CurvatureData.Case16.bad_polynomial_nonpos
  · exact Stage350CurvatureData.Case17.bad_polynomial_nonpos
  · exact Stage350CurvatureData.Case18.bad_polynomial_nonpos
  · exact Stage350CurvatureData.Case19.bad_polynomial_nonpos
  · exact Stage350CurvatureData.Case20.bad_polynomial_nonpos
  · exact Stage350CurvatureData.Case21.bad_polynomial_nonpos
  · exact Stage350CurvatureData.Case22.bad_polynomial_nonpos
  · exact Stage350CurvatureData.Case23.bad_polynomial_nonpos

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
#print axioms main_positive
#print axioms bad_polynomial_nonpos
end ForestUnimodality.Stage350CurvatureTable
