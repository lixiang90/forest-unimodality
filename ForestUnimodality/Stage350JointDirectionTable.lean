import ForestUnimodality.Stage350JointInputsData.Case04
import ForestUnimodality.Stage350JointInputsData.Case05
import ForestUnimodality.Stage350JointInputsData.Case06
import ForestUnimodality.Stage350JointInputsData.Case24
import ForestUnimodality.Stage350JointInputsData.Case25
import ForestUnimodality.Stage350JointInputsData.Case26
import ForestUnimodality.Stage350JointInputsData.Case27
import ForestUnimodality.Stage350JointInputsData.Case28
import ForestUnimodality.Stage350JointInputsData.Case29
import ForestUnimodality.Stage350JointInputsData.Case30
import ForestUnimodality.Stage350JointInputsData.Case31
import ForestUnimodality.Stage350JointInputsData.Case32
import ForestUnimodality.Stage350JointInputsData.Case33
import ForestUnimodality.Stage350JointInputsData.Case34
import ForestUnimodality.Stage350JointInputsData.Case35
import ForestUnimodality.JointDirectionCoefficient

namespace ForestUnimodality.Stage350JointDirectionTable
open JointDirectionBudget ReciprocalGradientBudget

noncomputable def row (i:Fin 15) : Parameters := ![Stage350JointDirectionData.Case04.parameters, Stage350JointDirectionData.Case05.parameters, Stage350JointDirectionData.Case06.parameters, Stage350JointDirectionData.Case24.parameters, Stage350JointDirectionData.Case25.parameters, Stage350JointDirectionData.Case26.parameters, Stage350JointDirectionData.Case27.parameters, Stage350JointDirectionData.Case28.parameters, Stage350JointDirectionData.Case29.parameters, Stage350JointDirectionData.Case30.parameters, Stage350JointDirectionData.Case31.parameters, Stage350JointDirectionData.Case32.parameters, Stage350JointDirectionData.Case33.parameters, Stage350JointDirectionData.Case34.parameters, Stage350JointDirectionData.Case35.parameters] i

def sourceIndex (i:Fin 15) : Fin 43 := ![3, 4, 5, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34] i

noncomputable def theta (i:Fin 15) : ℝ := ![Stage350JointInputsData.Case04.theta, Stage350JointInputsData.Case05.theta, Stage350JointInputsData.Case06.theta, Stage350JointInputsData.Case24.theta, Stage350JointInputsData.Case25.theta, Stage350JointInputsData.Case26.theta, Stage350JointInputsData.Case27.theta, Stage350JointInputsData.Case28.theta, Stage350JointInputsData.Case29.theta, Stage350JointInputsData.Case30.theta, Stage350JointInputsData.Case31.theta, Stage350JointInputsData.Case32.theta, Stage350JointInputsData.Case33.theta, Stage350JointInputsData.Case34.theta, Stage350JointInputsData.Case35.theta] i

def reverse (i:Fin 15) : Bool := ![Stage350JointInputsData.Case04.reverse, Stage350JointInputsData.Case05.reverse, Stage350JointInputsData.Case06.reverse, Stage350JointInputsData.Case24.reverse, Stage350JointInputsData.Case25.reverse, Stage350JointInputsData.Case26.reverse, Stage350JointInputsData.Case27.reverse, Stage350JointInputsData.Case28.reverse, Stage350JointInputsData.Case29.reverse, Stage350JointInputsData.Case30.reverse, Stage350JointInputsData.Case31.reverse, Stage350JointInputsData.Case32.reverse, Stage350JointInputsData.Case33.reverse, Stage350JointInputsData.Case34.reverse, Stage350JointInputsData.Case35.reverse] i

noncomputable def profiles (i:Fin 15) : ℕ→GradientProfile := ![Stage350JointInputsData.Case04.profiles, Stage350JointInputsData.Case05.profiles, Stage350JointInputsData.Case06.profiles, Stage350JointInputsData.Case24.profiles, Stage350JointInputsData.Case25.profiles, Stage350JointInputsData.Case26.profiles, Stage350JointInputsData.Case27.profiles, Stage350JointInputsData.Case28.profiles, Stage350JointInputsData.Case29.profiles, Stage350JointInputsData.Case30.profiles, Stage350JointInputsData.Case31.profiles, Stage350JointInputsData.Case32.profiles, Stage350JointInputsData.Case33.profiles, Stage350JointInputsData.Case34.profiles, Stage350JointInputsData.Case35.profiles] i

noncomputable def lower (i:Fin 15) : ℝ := (Stage350SourceTable.row (sourceIndex i)).a
noncomputable def upper (i:Fin 15) : ℝ := (Stage350SourceTable.row (sourceIndex i)).b

theorem row_valid (i:Fin 15) : Valid (row i) := by
  fin_cases i
  · exact Stage350JointDirectionData.Case04.parameters_valid
  · exact Stage350JointDirectionData.Case05.parameters_valid
  · exact Stage350JointDirectionData.Case06.parameters_valid
  · exact Stage350JointDirectionData.Case24.parameters_valid
  · exact Stage350JointDirectionData.Case25.parameters_valid
  · exact Stage350JointDirectionData.Case26.parameters_valid
  · exact Stage350JointDirectionData.Case27.parameters_valid
  · exact Stage350JointDirectionData.Case28.parameters_valid
  · exact Stage350JointDirectionData.Case29.parameters_valid
  · exact Stage350JointDirectionData.Case30.parameters_valid
  · exact Stage350JointDirectionData.Case31.parameters_valid
  · exact Stage350JointDirectionData.Case32.parameters_valid
  · exact Stage350JointDirectionData.Case33.parameters_valid
  · exact Stage350JointDirectionData.Case34.parameters_valid
  · exact Stage350JointDirectionData.Case35.parameters_valid

theorem margin_positive (i:Fin 15) : 0<margin (row i) (row i).start := by
  fin_cases i
  · exact Stage350JointDirectionData.Case04.margin_positive
  · exact Stage350JointDirectionData.Case05.margin_positive
  · exact Stage350JointDirectionData.Case06.margin_positive
  · exact Stage350JointDirectionData.Case24.margin_positive
  · exact Stage350JointDirectionData.Case25.margin_positive
  · exact Stage350JointDirectionData.Case26.margin_positive
  · exact Stage350JointDirectionData.Case27.margin_positive
  · exact Stage350JointDirectionData.Case28.margin_positive
  · exact Stage350JointDirectionData.Case29.margin_positive
  · exact Stage350JointDirectionData.Case30.margin_positive
  · exact Stage350JointDirectionData.Case31.margin_positive
  · exact Stage350JointDirectionData.Case32.margin_positive
  · exact Stage350JointDirectionData.Case33.margin_positive
  · exact Stage350JointDirectionData.Case34.margin_positive
  · exact Stage350JointDirectionData.Case35.margin_positive

theorem envelope_valid (i:Fin 15) : JointDirectionActual.Envelope (row i) (theta i) := by
  fin_cases i
  · exact Stage350JointInputsData.Case04.envelope_valid
  · exact Stage350JointInputsData.Case05.envelope_valid
  · exact Stage350JointInputsData.Case06.envelope_valid
  · exact Stage350JointInputsData.Case24.envelope_valid
  · exact Stage350JointInputsData.Case25.envelope_valid
  · exact Stage350JointInputsData.Case26.envelope_valid
  · exact Stage350JointInputsData.Case27.envelope_valid
  · exact Stage350JointInputsData.Case28.envelope_valid
  · exact Stage350JointInputsData.Case29.envelope_valid
  · exact Stage350JointInputsData.Case30.envelope_valid
  · exact Stage350JointInputsData.Case31.envelope_valid
  · exact Stage350JointInputsData.Case32.envelope_valid
  · exact Stage350JointInputsData.Case33.envelope_valid
  · exact Stage350JointInputsData.Case34.envelope_valid
  · exact Stage350JointInputsData.Case35.envelope_valid

theorem start_match (i:Fin 15) : (row i).start=((Stage350SourceTable.row (sourceIndex i)).start:ℝ) := by
  fin_cases i
  · exact Stage350JointInputsData.Case04.scalar_valid.start_match
  · exact Stage350JointInputsData.Case05.scalar_valid.start_match
  · exact Stage350JointInputsData.Case06.scalar_valid.start_match
  · exact Stage350JointInputsData.Case24.scalar_valid.start_match
  · exact Stage350JointInputsData.Case25.scalar_valid.start_match
  · exact Stage350JointInputsData.Case26.scalar_valid.start_match
  · exact Stage350JointInputsData.Case27.scalar_valid.start_match
  · exact Stage350JointInputsData.Case28.scalar_valid.start_match
  · exact Stage350JointInputsData.Case29.scalar_valid.start_match
  · exact Stage350JointInputsData.Case30.scalar_valid.start_match
  · exact Stage350JointInputsData.Case31.scalar_valid.start_match
  · exact Stage350JointInputsData.Case32.scalar_valid.start_match
  · exact Stage350JointInputsData.Case33.scalar_valid.start_match
  · exact Stage350JointInputsData.Case34.scalar_valid.start_match
  · exact Stage350JointInputsData.Case35.scalar_valid.start_match

variable {V:Type*} [DecidableEq V]
theorem actual_inputs (i:Fin 15) {G:SimpleGraph V} {S B:Finset V} {z:ℝ} (k:ℕ)
    (hB:IsMaximumMarginalIndependentOn G S B z) (hG:G.IsAcyclic) (hn:0<S.card)
    (hs:(row i).start≤hardCoreAvailableMean G S B z)
    (hlo:lower i≤z) (hhi:z≤upper i) (hrank:(S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean:hardCoreMean G S z=k) :
    JointDirectionActual.Inputs (row i) G S B z (hardCoreAvailableMean G S B z)
      (Stage350JointInputs.ratio (reverse i) z) (theta i) k (reverse i) (profiles i) := by
  fin_cases i
  · exact Stage350JointInputsData.Case04.actual_inputs k hB hG hn hs hlo hhi hrank hmean
  · exact Stage350JointInputsData.Case05.actual_inputs k hB hG hn hs hlo hhi hrank hmean
  · exact Stage350JointInputsData.Case06.actual_inputs k hB hG hn hs hlo hhi hrank hmean
  · exact Stage350JointInputsData.Case24.actual_inputs k hB hG hn hs hlo hhi hrank hmean
  · exact Stage350JointInputsData.Case25.actual_inputs k hB hG hn hs hlo hhi hrank hmean
  · exact Stage350JointInputsData.Case26.actual_inputs k hB hG hn hs hlo hhi hrank hmean
  · exact Stage350JointInputsData.Case27.actual_inputs k hB hG hn hs hlo hhi hrank hmean
  · exact Stage350JointInputsData.Case28.actual_inputs k hB hG hn hs hlo hhi hrank hmean
  · exact Stage350JointInputsData.Case29.actual_inputs k hB hG hn hs hlo hhi hrank hmean
  · exact Stage350JointInputsData.Case30.actual_inputs k hB hG hn hs hlo hhi hrank hmean
  · exact Stage350JointInputsData.Case31.actual_inputs k hB hG hn hs hlo hhi hrank hmean
  · exact Stage350JointInputsData.Case32.actual_inputs k hB hG hn hs hlo hhi hrank hmean
  · exact Stage350JointInputsData.Case33.actual_inputs k hB hG hn hs hlo hhi hrank hmean
  · exact Stage350JointInputsData.Case34.actual_inputs k hB hG hn hs hlo hhi hrank hmean
  · exact Stage350JointInputsData.Case35.actual_inputs k hB hG hn hs hlo hhi hrank hmean

theorem covers_left {z:ℝ} (hlo:((7/10):ℝ)≤z)
    (hhi:z≤((22/25):ℝ)) :
    ∃i:Fin 15,reverse i=true ∧ lower i≤z ∧ z≤upper i := by
  by_cases h0:z≤((4/5):ℝ)
  · refine ⟨0,by decide,?_⟩
    change (((7/10):ℚ):ℝ)≤z ∧ z≤(((4/5):ℚ):ℝ)
    norm_num
    constructor <;> linarith
  by_cases h1:z≤((17/20):ℝ)
  · refine ⟨1,by decide,?_⟩
    change (((4/5):ℚ):ℝ)≤z ∧ z≤(((17/20):ℚ):ℝ)
    norm_num
    constructor <;> linarith
  refine ⟨2,by decide,?_⟩
  change (((17/20):ℚ):ℝ)≤z ∧ z≤(((22/25):ℚ):ℝ)
  norm_num
  constructor <;> linarith

theorem covers_right {z:ℝ} (hlo:((57/50):ℝ)≤z)
    (hhi:z≤((7/5):ℝ)) :
    ∃i:Fin 15,reverse i=false ∧ lower i≤z ∧ z≤upper i := by
  by_cases h0:z≤((29/25):ℝ)
  · refine ⟨3,by decide,?_⟩
    change (((57/50):ℚ):ℝ)≤z ∧ z≤(((29/25):ℚ):ℝ)
    norm_num
    constructor <;> linarith
  by_cases h1:z≤((6/5):ℝ)
  · refine ⟨4,by decide,?_⟩
    change (((29/25):ℚ):ℝ)≤z ∧ z≤(((6/5):ℚ):ℝ)
    norm_num
    constructor <;> linarith
  by_cases h2:z≤((97/80):ℝ)
  · refine ⟨5,by decide,?_⟩
    change (((6/5):ℚ):ℝ)≤z ∧ z≤(((97/80):ℚ):ℝ)
    norm_num
    constructor <;> linarith
  by_cases h3:z≤((49/40):ℝ)
  · refine ⟨6,by decide,?_⟩
    change (((97/80):ℚ):ℝ)≤z ∧ z≤(((49/40):ℚ):ℝ)
    norm_num
    constructor <;> linarith
  by_cases h4:z≤((99/80):ℝ)
  · refine ⟨7,by decide,?_⟩
    change (((49/40):ℚ):ℝ)≤z ∧ z≤(((99/80):ℚ):ℝ)
    norm_num
    constructor <;> linarith
  by_cases h5:z≤((5/4):ℝ)
  · refine ⟨8,by decide,?_⟩
    change (((99/80):ℚ):ℝ)≤z ∧ z≤(((5/4):ℚ):ℝ)
    norm_num
    constructor <;> linarith
  by_cases h6:z≤((13/10):ℝ)
  · refine ⟨9,by decide,?_⟩
    change (((5/4):ℚ):ℝ)≤z ∧ z≤(((13/10):ℚ):ℝ)
    norm_num
    constructor <;> linarith
  by_cases h7:z≤((21/16):ℝ)
  · refine ⟨10,by decide,?_⟩
    change (((13/10):ℚ):ℝ)≤z ∧ z≤(((21/16):ℚ):ℝ)
    norm_num
    constructor <;> linarith
  by_cases h8:z≤((53/40):ℝ)
  · refine ⟨11,by decide,?_⟩
    change (((21/16):ℚ):ℝ)≤z ∧ z≤(((53/40):ℚ):ℝ)
    norm_num
    constructor <;> linarith
  by_cases h9:z≤((107/80):ℝ)
  · refine ⟨12,by decide,?_⟩
    change (((53/40):ℚ):ℝ)≤z ∧ z≤(((107/80):ℚ):ℝ)
    norm_num
    constructor <;> linarith
  by_cases h10:z≤((27/20):ℝ)
  · refine ⟨13,by decide,?_⟩
    change (((107/80):ℚ):ℝ)≤z ∧ z≤(((27/20):ℚ):ℝ)
    norm_num
    constructor <;> linarith
  refine ⟨14,by decide,?_⟩
  change (((27/20):ℚ):ℝ)≤z ∧ z≤(((7/5):ℚ):ℝ)
  norm_num
  constructor <;> linarith

#print axioms row_valid
#print axioms margin_positive
#print axioms actual_inputs
#print axioms covers_left
#print axioms covers_right
end ForestUnimodality.Stage350JointDirectionTable
