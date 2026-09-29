import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell314.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell314
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(1124634877104212079569998359/10000000000000000000000000000)]
def R : ℚ := (1706358982962962962962962962963/1000000000000000000000000000000)
def D : ℚ := (1157460523940042826552462526767/500000000000000000000000000000)
def vmax : ℚ := (128425/550564)
def mlo : ℚ := (2242426740139884265042540314037/40000000000000000000000000000)
def mhi : ℚ := (51575815023217338095978427222851/800000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (9354054324546266979902708903545243723230310719869736213375632623761204436314222319798710753/27528200000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2586117121866621104686601/200000000000000000000000)) (.exp (-2521911321312417657083702377981466479540277697115434665283/400000000000000000000000000000000000000000000000000000000) (1827551285960481266517/1000000000000000000000000) (913775642980240633259/500000000000000000000000) { parts := 7, inner := (-2521911321312417657083702377981466479540277697115434665283/2800000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (203146111996897298199284098953/500000000000000000000000000000), innerHi := (406292223993794596398568197907/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (1432990797436096614652047440485583080186544486853125884332305166628563608668065588392750387187/4404512000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2586117121866621104686601/200000000000000000000000)) (.exp (-58003960390185606112925154693573729029426387033654997301509/8000000000000000000000000000000000000000000000000000000000) (709822904890621835193/1000000000000000000000000) (354911452445310917597/500000000000000000000000) { parts := 8, inner := (-58003960390185606112925154693573729029426387033654997301509/64000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (404011522213737653270587781521/1000000000000000000000000000000), innerHi := (202005761106868826635293890761/500000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_hi_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms (∅ : Finset ℤ)
    row.A row.B row.dδ row.dM (R * vmax : ℚ) 0 D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ)) (fun _ => 0) (fun _ => 0)
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage170KernelData.Cell314
