import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell140.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell140
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(49323073245493994929346395681/500000000000000000000000000000)]
def alpha : ℚ := (171271353038703617532923268739/1000000000000000000000000000000)
def D : ℚ := (740545898666666666666666666667/500000000000000000000000000000)
def mlo : ℚ := (16352259149444616542018852060007/1000000000000000000000000000000)
def mhi : ℚ := (8849457892640616010974908173651/400000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (112014426092272081405551026541646096962820232109111214846995301765972503154941268075457/100000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5422188751100357251289097/1000000000000000000000000)) (.exp (-806543675757356155876118306008611573271616147078667377629767/500000000000000000000000000000000000000000000000000000000000) (9963572120287900675959/50000000000000000000000) (199271442405758013519181/1000000000000000000000000) { parts := 2, inner := (-806543675757356155876118306008611573271616147078667377629767/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (1394994688070076702961728999/3125000000000000000000000000), innerHi := (446398300182424544947753279681/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (52089008698437698714524162794559926091102645325374623028539976583624126064384691109453/80000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5422188751100357251289097/1000000000000000000000000)) (.exp (-436482459821628037297664024428197336122900402206503304401331/200000000000000000000000000000000000000000000000000000000000) (56384584648746121412771/500000000000000000000000) (112769169297492242825543/1000000000000000000000000) { parts := 3, inner := (-436482459821628037297664024428197336122900402206503304401331/600000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (96625878641312050736349437469/200000000000000000000000000000), innerHi := (241564696603280126840873593673/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell140
