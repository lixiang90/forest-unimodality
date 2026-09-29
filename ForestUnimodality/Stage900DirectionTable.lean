import ForestUnimodality.Stage900DirectionData.Case01
import ForestUnimodality.Stage900DirectionData.Case02
import ForestUnimodality.Stage900DirectionData.Case03
import ForestUnimodality.Stage900DirectionData.Case04
import ForestUnimodality.Stage900DirectionData.Case05
import ForestUnimodality.Stage900DirectionData.Case23
import ForestUnimodality.Stage900DirectionData.Case24
import ForestUnimodality.Stage900DirectionData.Case25
import ForestUnimodality.Stage900DirectionData.Case26
import ForestUnimodality.Stage900DirectionData.Case27
import ForestUnimodality.Stage900DirectionData.Case28

namespace ForestUnimodality.Stage900DirectionTable
open DirectionBudget

noncomputable def row (i : Fin 11) : Parameters :=
  ![Stage900DirectionData.Case01.parameters, Stage900DirectionData.Case02.parameters, Stage900DirectionData.Case03.parameters, Stage900DirectionData.Case04.parameters, Stage900DirectionData.Case05.parameters, Stage900DirectionData.Case23.parameters, Stage900DirectionData.Case24.parameters, Stage900DirectionData.Case25.parameters, Stage900DirectionData.Case26.parameters, Stage900DirectionData.Case27.parameters, Stage900DirectionData.Case28.parameters] i

def isLeft (i : Fin 11) : Bool := decide (i.val < 5)

def selectionIndex (i : Fin 11) : Fin 28 :=
  ![0, 1, 2, 3, 4, 22, 23, 24, 25, 26, 27] i

theorem row_valid (i : Fin 11) : (row i).Valid := by
  fin_cases i
  · exact Stage900DirectionData.Case01.parameters_valid
  · exact Stage900DirectionData.Case02.parameters_valid
  · exact Stage900DirectionData.Case03.parameters_valid
  · exact Stage900DirectionData.Case04.parameters_valid
  · exact Stage900DirectionData.Case05.parameters_valid
  · exact Stage900DirectionData.Case23.parameters_valid
  · exact Stage900DirectionData.Case24.parameters_valid
  · exact Stage900DirectionData.Case25.parameters_valid
  · exact Stage900DirectionData.Case26.parameters_valid
  · exact Stage900DirectionData.Case27.parameters_valid
  · exact Stage900DirectionData.Case28.parameters_valid

theorem bracket_positive (i : Fin 11) : 0 <
    PointMassBudgetMonotonicity.mainBracket (row i).R (row i).D (row i).rate0 (row i).start := by
  fin_cases i
  · exact Stage900DirectionData.Case01.bracket_positive
  · exact Stage900DirectionData.Case02.bracket_positive
  · exact Stage900DirectionData.Case03.bracket_positive
  · exact Stage900DirectionData.Case04.bracket_positive
  · exact Stage900DirectionData.Case05.bracket_positive
  · exact Stage900DirectionData.Case23.bracket_positive
  · exact Stage900DirectionData.Case24.bracket_positive
  · exact Stage900DirectionData.Case25.bracket_positive
  · exact Stage900DirectionData.Case26.bracket_positive
  · exact Stage900DirectionData.Case27.bracket_positive
  · exact Stage900DirectionData.Case28.bracket_positive

theorem mass_positive (i : Fin 11) : 0 < (row i).mass (row i).start := by
  fin_cases i
  · exact Stage900DirectionData.Case01.mass_positive
  · exact Stage900DirectionData.Case02.mass_positive
  · exact Stage900DirectionData.Case03.mass_positive
  · exact Stage900DirectionData.Case04.mass_positive
  · exact Stage900DirectionData.Case05.mass_positive
  · exact Stage900DirectionData.Case23.mass_positive
  · exact Stage900DirectionData.Case24.mass_positive
  · exact Stage900DirectionData.Case25.mass_positive
  · exact Stage900DirectionData.Case26.mass_positive
  · exact Stage900DirectionData.Case27.mass_positive
  · exact Stage900DirectionData.Case28.mass_positive

theorem margin_positive (i : Fin 11) :
    if isLeft i then 0 < (row i).leftMargin (row i).start
    else 0 < (row i).rightMargin (row i).start := by
  fin_cases i
  · exact Stage900DirectionData.Case01.margin_positive
  · exact Stage900DirectionData.Case02.margin_positive
  · exact Stage900DirectionData.Case03.margin_positive
  · exact Stage900DirectionData.Case04.margin_positive
  · exact Stage900DirectionData.Case05.margin_positive
  · exact Stage900DirectionData.Case23.margin_positive
  · exact Stage900DirectionData.Case24.margin_positive
  · exact Stage900DirectionData.Case25.margin_positive
  · exact Stage900DirectionData.Case26.margin_positive
  · exact Stage900DirectionData.Case27.margin_positive
  · exact Stage900DirectionData.Case28.margin_positive

theorem covers_left {z : ℝ} (hlo : (1/3 : ℝ) ≤ z)
    (hhi : z ≤ (22/25 : ℝ)) :
    ∃ i : Fin 11, isLeft i = true ∧ (row i).a ≤ z ∧ z ≤ (row i).b := by
  by_cases h0 : z ≤ (1/2 : ℝ)
  · refine ⟨0, by decide, ?_⟩
    change (1/3 : ℝ) ≤ z ∧ z ≤ (1/2 : ℝ)
    constructor <;> linarith
  by_cases h1 : z ≤ (7/10 : ℝ)
  · refine ⟨1, by decide, ?_⟩
    change (1/2 : ℝ) ≤ z ∧ z ≤ (7/10 : ℝ)
    constructor <;> linarith
  by_cases h2 : z ≤ (4/5 : ℝ)
  · refine ⟨2, by decide, ?_⟩
    change (7/10 : ℝ) ≤ z ∧ z ≤ (4/5 : ℝ)
    constructor <;> linarith
  by_cases h3 : z ≤ (17/20 : ℝ)
  · refine ⟨3, by decide, ?_⟩
    change (4/5 : ℝ) ≤ z ∧ z ≤ (17/20 : ℝ)
    constructor <;> linarith
  refine ⟨4, by decide, ?_⟩
  change (17/20 : ℝ) ≤ z ∧ z ≤ (22/25 : ℝ)
  constructor <;> linarith

theorem covers_right {z : ℝ} (hlo : (57/50 : ℝ) ≤ z)
    (hhi : z ≤ (9/4 : ℝ)) :
    ∃ i : Fin 11, isLeft i = false ∧ (row i).a ≤ z ∧ z ≤ (row i).b := by
  by_cases h0 : z ≤ (29/25 : ℝ)
  · refine ⟨5, by decide, ?_⟩
    change (57/50 : ℝ) ≤ z ∧ z ≤ (29/25 : ℝ)
    constructor <;> linarith
  by_cases h1 : z ≤ (6/5 : ℝ)
  · refine ⟨6, by decide, ?_⟩
    change (29/25 : ℝ) ≤ z ∧ z ≤ (6/5 : ℝ)
    constructor <;> linarith
  by_cases h2 : z ≤ (13/10 : ℝ)
  · refine ⟨7, by decide, ?_⟩
    change (6/5 : ℝ) ≤ z ∧ z ≤ (13/10 : ℝ)
    constructor <;> linarith
  by_cases h3 : z ≤ (3/2 : ℝ)
  · refine ⟨8, by decide, ?_⟩
    change (13/10 : ℝ) ≤ z ∧ z ≤ (3/2 : ℝ)
    constructor <;> linarith
  by_cases h4 : z ≤ (9/5 : ℝ)
  · refine ⟨9, by decide, ?_⟩
    change (3/2 : ℝ) ≤ z ∧ z ≤ (9/5 : ℝ)
    constructor <;> linarith
  refine ⟨10, by decide, ?_⟩
  change (9/5 : ℝ) ≤ z ∧ z ≤ (9/4 : ℝ)
  constructor <;> linarith

#print axioms row_valid
#print axioms margin_positive
#print axioms covers_left
#print axioms covers_right
end ForestUnimodality.Stage900DirectionTable
