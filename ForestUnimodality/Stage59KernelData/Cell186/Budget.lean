import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell186.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell186
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(6325241910714911448304525909/62500000000000000000000000000)]
def alpha : ℚ := (47164835055065117813560215093/250000000000000000000000000000)
def D : ℚ := (378417184464601769911504424779/250000000000000000000000000000)
def mlo : ℚ := (3389416284545792539348122443921/200000000000000000000000000000)
def mhi : ℚ := (27303631181063328789193208576031/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (231110231567679802528901161293933595058387790231623183262069995164813822103603833743/125000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (31355935835393694555151/3125000000000000000000)) (.exp (-21438877935868664788941645803744407246745266162286344049189/12500000000000000000000000000000000000000000000000000000000) (179943883529240639779629/1000000000000000000000000) (17994388352924063977963/100000000000000000000000) { parts := 2, inner := (-21438877935868664788941645803744407246745266162286344049189/25000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (424197929661662351423022228203/1000000000000000000000000000000), innerHi := (106049482415415587855755557051/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (422722695822769446216526621380794403087258048368577958907368877781511930633509351873/625000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (31355935835393694555151/3125000000000000000000)) (.exp (-172702072261164244133141035641278959940161271521130435887179/62500000000000000000000000000000000000000000000000000000000) (63087466635372409154651/1000000000000000000000000) (15771866658843102288663/250000000000000000000000) { parts := 3, inner := (-57567357420388081377713678547092986646720423840376811962393/62500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (15923591240141930057431530093/40000000000000000000000000000), innerHi := (199044890501774125717894126163/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell186
