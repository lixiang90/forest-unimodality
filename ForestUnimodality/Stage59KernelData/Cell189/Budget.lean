import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell189.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell189
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(50813704576437186363577576573/500000000000000000000000000000)]
def alpha : ℚ := (189754607486393205055170884623/1000000000000000000000000000000)
def D : ℚ := (756040265055283011089582388589/500000000000000000000000000000)
def mlo : ℚ := (4226948162344286111712157274891/250000000000000000000000000000)
def mhi : ℚ := (27240332601774288275478346882631/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (579111383894490304280149400279937021360312440220658830038049155088132423399729076869/312500000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4982894534664207952801007/500000000000000000000000)) (.exp (-214786895181276606178287511546826806761643790472701562728543/125000000000000000000000000000000000000000000000000000000000) (35874337431390639153037/200000000000000000000000) (89685843578476597882593/500000000000000000000000) { parts := 2, inner := (-214786895181276606178287511546826806761643790472701562728543/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (423522947615537351729727607853/1000000000000000000000000000000), innerHi := (211761473807768675864863803927/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (863843204550070556693043121688985472506148808944868275153003678985917729422855995529/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4982894534664207952801007/500000000000000000000000)) (.exp (-1384182213390449239815630629968445067319990698289228246203563/500000000000000000000000000000000000000000000000000000000000) (12552915379646898260199/200000000000000000000000) (15691144224558622825249/250000000000000000000000) { parts := 3, inner := (-1384182213390449239815630629968445067319990698289228246203563/1500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (198704730428546356063943482389/500000000000000000000000000000), innerHi := (397409460857092712127886964779/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_hi_positive : 0 < budget mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < budget m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms row.fixedIndices
    row.A row.B row.dδ row.dM alpha varianceIntercept D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell189
