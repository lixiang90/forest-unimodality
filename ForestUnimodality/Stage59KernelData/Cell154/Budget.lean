import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell154.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell154
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(49834869859636637506232445169/500000000000000000000000000000)]
def alpha : ℚ := (86667229202065759637188208617/500000000000000000000000000000)
def D : ℚ := (1485999802888308295231874591771/1000000000000000000000000000000)
def mlo : ℚ := (2028409090909090909090909090909/125000000000000000000000000000)
def mhi : ℚ := (4390909090909090909090909090909/200000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (549674602243739811368763788914275641726570724446785697952870084061902583649665810611/312500000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (8537632728631034950694811/1000000000000000000000000)) (.exp (-101085503067558406759801039348478424102740033032953978868621/62500000000000000000000000000000000000000000000000000000000) (12401265299176668437811/62500000000000000000000) (198420244786826695004977/1000000000000000000000000) { parts := 2, inner := (-101085503067558406759801039348478424102740033032953978868621/125000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (222721936945390886099068633107/500000000000000000000000000000), innerHi := (89088774778156354439627453243/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (511070718065877142253094315190673394430215601151984083902870084061902583649665810611/500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (8537632728631034950694811/1000000000000000000000000)) (.exp (-218820383110949962868275191060240924102740033032953978868621/100000000000000000000000000000000000000000000000000000000000) (56058975320918144899441/500000000000000000000000) (112117950641836289798883/1000000000000000000000000) { parts := 3, inner := (-218820383110949962868275191060240924102740033032953978868621/300000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (482197606460889297987742248747/1000000000000000000000000000000), innerHi := (120549401615222324496935562187/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell154
