import ForestUnimodality.Stage350PlainDirectionData.Case01
import ForestUnimodality.Stage350PlainDirectionData.Case02
import ForestUnimodality.Stage350PlainDirectionData.Case03
import ForestUnimodality.Stage350PlainDirectionData.Case36
import ForestUnimodality.Stage350PlainDirectionData.Case37
import ForestUnimodality.Stage350PlainDirectionData.Case38
import ForestUnimodality.Stage350PlainDirectionData.Case39
import ForestUnimodality.Stage350PlainDirectionData.Case40
import ForestUnimodality.Stage350PlainDirectionData.Case41
import ForestUnimodality.Stage350PlainDirectionData.Case42
import ForestUnimodality.Stage350PlainDirectionData.Case43

namespace ForestUnimodality.Stage350PlainDirectionTable
open DirectionBudget

noncomputable def row (i : Fin 11) : Parameters :=
  ![Stage350PlainDirectionData.Case01.parameters, Stage350PlainDirectionData.Case02.parameters, Stage350PlainDirectionData.Case03.parameters, Stage350PlainDirectionData.Case36.parameters, Stage350PlainDirectionData.Case37.parameters, Stage350PlainDirectionData.Case38.parameters, Stage350PlainDirectionData.Case39.parameters, Stage350PlainDirectionData.Case40.parameters, Stage350PlainDirectionData.Case41.parameters, Stage350PlainDirectionData.Case42.parameters, Stage350PlainDirectionData.Case43.parameters] i

def isLeft (i : Fin 11) : Bool := decide (i.val < 3)

def sourceIndex (i : Fin 11) : Fin 43 :=
  ![0, 1, 2, 35, 36, 37, 38, 39, 40, 41, 42] i

theorem row_valid (i : Fin 11) : (row i).Valid := by
  fin_cases i
  · exact Stage350PlainDirectionData.Case01.parameters_valid
  · exact Stage350PlainDirectionData.Case02.parameters_valid
  · exact Stage350PlainDirectionData.Case03.parameters_valid
  · exact Stage350PlainDirectionData.Case36.parameters_valid
  · exact Stage350PlainDirectionData.Case37.parameters_valid
  · exact Stage350PlainDirectionData.Case38.parameters_valid
  · exact Stage350PlainDirectionData.Case39.parameters_valid
  · exact Stage350PlainDirectionData.Case40.parameters_valid
  · exact Stage350PlainDirectionData.Case41.parameters_valid
  · exact Stage350PlainDirectionData.Case42.parameters_valid
  · exact Stage350PlainDirectionData.Case43.parameters_valid

theorem bracket_positive (i : Fin 11) : 0 <
    PointMassBudgetMonotonicity.mainBracket (row i).R (row i).D (row i).rate0 (row i).start := by
  fin_cases i
  · exact Stage350PlainDirectionData.Case01.bracket_positive
  · exact Stage350PlainDirectionData.Case02.bracket_positive
  · exact Stage350PlainDirectionData.Case03.bracket_positive
  · exact Stage350PlainDirectionData.Case36.bracket_positive
  · exact Stage350PlainDirectionData.Case37.bracket_positive
  · exact Stage350PlainDirectionData.Case38.bracket_positive
  · exact Stage350PlainDirectionData.Case39.bracket_positive
  · exact Stage350PlainDirectionData.Case40.bracket_positive
  · exact Stage350PlainDirectionData.Case41.bracket_positive
  · exact Stage350PlainDirectionData.Case42.bracket_positive
  · exact Stage350PlainDirectionData.Case43.bracket_positive

theorem mass_positive (i : Fin 11) : 0 < (row i).mass (row i).start := by
  fin_cases i
  · exact Stage350PlainDirectionData.Case01.mass_positive
  · exact Stage350PlainDirectionData.Case02.mass_positive
  · exact Stage350PlainDirectionData.Case03.mass_positive
  · exact Stage350PlainDirectionData.Case36.mass_positive
  · exact Stage350PlainDirectionData.Case37.mass_positive
  · exact Stage350PlainDirectionData.Case38.mass_positive
  · exact Stage350PlainDirectionData.Case39.mass_positive
  · exact Stage350PlainDirectionData.Case40.mass_positive
  · exact Stage350PlainDirectionData.Case41.mass_positive
  · exact Stage350PlainDirectionData.Case42.mass_positive
  · exact Stage350PlainDirectionData.Case43.mass_positive

theorem margin_positive (i : Fin 11) :
    if isLeft i then 0 < (row i).leftMargin (row i).start
    else 0 < (row i).rightMargin (row i).start := by
  fin_cases i
  · exact Stage350PlainDirectionData.Case01.margin_positive
  · exact Stage350PlainDirectionData.Case02.margin_positive
  · exact Stage350PlainDirectionData.Case03.margin_positive
  · exact Stage350PlainDirectionData.Case36.margin_positive
  · exact Stage350PlainDirectionData.Case37.margin_positive
  · exact Stage350PlainDirectionData.Case38.margin_positive
  · exact Stage350PlainDirectionData.Case39.margin_positive
  · exact Stage350PlainDirectionData.Case40.margin_positive
  · exact Stage350PlainDirectionData.Case41.margin_positive
  · exact Stage350PlainDirectionData.Case42.margin_positive
  · exact Stage350PlainDirectionData.Case43.margin_positive

theorem covers_left {z : ℝ} (hlo : (1/3 : ℝ) ≤ z)
    (hhi : z ≤ (7/10 : ℝ)) :
    ∃ i : Fin 11, isLeft i = true ∧ (row i).a ≤ z ∧ z ≤ (row i).b := by
  by_cases h0 : z ≤ (2/5 : ℝ)
  · refine ⟨0, by decide, ?_⟩
    change (1/3 : ℝ) ≤ z ∧ z ≤ (2/5 : ℝ)
    constructor <;> linarith
  by_cases h1 : z ≤ (1/2 : ℝ)
  · refine ⟨1, by decide, ?_⟩
    change (2/5 : ℝ) ≤ z ∧ z ≤ (1/2 : ℝ)
    constructor <;> linarith
  refine ⟨2, by decide, ?_⟩
  change (1/2 : ℝ) ≤ z ∧ z ≤ (7/10 : ℝ)
  constructor <;> linarith

theorem covers_right {z : ℝ} (hlo : (7/5 : ℝ) ≤ z)
    (hhi : z ≤ (9/4 : ℝ)) :
    ∃ i : Fin 11, isLeft i = false ∧ (row i).a ≤ z ∧ z ≤ (row i).b := by
  by_cases h0 : z ≤ (3/2 : ℝ)
  · refine ⟨3, by decide, ?_⟩
    change (7/5 : ℝ) ≤ z ∧ z ≤ (3/2 : ℝ)
    constructor <;> linarith
  by_cases h1 : z ≤ (123/80 : ℝ)
  · refine ⟨4, by decide, ?_⟩
    change (3/2 : ℝ) ≤ z ∧ z ≤ (123/80 : ℝ)
    constructor <;> linarith
  by_cases h2 : z ≤ (63/40 : ℝ)
  · refine ⟨5, by decide, ?_⟩
    change (123/80 : ℝ) ≤ z ∧ z ≤ (63/40 : ℝ)
    constructor <;> linarith
  by_cases h3 : z ≤ (129/80 : ℝ)
  · refine ⟨6, by decide, ?_⟩
    change (63/40 : ℝ) ≤ z ∧ z ≤ (129/80 : ℝ)
    constructor <;> linarith
  by_cases h4 : z ≤ (33/20 : ℝ)
  · refine ⟨7, by decide, ?_⟩
    change (129/80 : ℝ) ≤ z ∧ z ≤ (33/20 : ℝ)
    constructor <;> linarith
  by_cases h5 : z ≤ (9/5 : ℝ)
  · refine ⟨8, by decide, ?_⟩
    change (33/20 : ℝ) ≤ z ∧ z ≤ (9/5 : ℝ)
    constructor <;> linarith
  by_cases h6 : z ≤ (2 : ℝ)
  · refine ⟨9, by decide, ?_⟩
    change (9/5 : ℝ) ≤ z ∧ z ≤ (2 : ℝ)
    constructor <;> linarith
  refine ⟨10, by decide, ?_⟩
  change (2 : ℝ) ≤ z ∧ z ≤ (9/4 : ℝ)
  constructor <;> linarith

#print axioms row_valid
#print axioms margin_positive
#print axioms covers_left
#print axioms covers_right
end ForestUnimodality.Stage350PlainDirectionTable
