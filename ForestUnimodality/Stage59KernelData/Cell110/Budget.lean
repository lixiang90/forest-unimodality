import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell110.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell110
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(138740854997490730566660132527/1000000000000000000000000000000)]
def alpha : ℚ := (43351066913724253330811172179/250000000000000000000000000000)
def D : ℚ := (358122879137538654233387669/244140625000000000000000000)
def mlo : ℚ := (16752821886359288310694471015879/1000000000000000000000000000000)
def mhi : ℚ := (44345704993303998469485364453797/2000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (1461816017648328027897422049886077296855600170326023910594734487486610602953287025207/3125000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4761077211026514710567881/1000000000000000000000000)) (.exp (-2324300832134163153535628051461975168934516198934154461396233/1000000000000000000000000000000000000000000000000000000000000) (97851834998832023670409/1000000000000000000000000) (9785183499883202367041/100000000000000000000000) { parts := 3, inner := (-2324300832134163153535628051461975168934516198934154461396233/3000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (23040558163565007258418942951/50000000000000000000000000000), innerHi := (460811163271300145168378859021/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (1107659752871687541812797330931234227767047020352993620300927615015902320802648513831/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4761077211026514710567881/1000000000000000000000000)) (.exp (-6152561026237490700535486018575767656289602588685502988355019/2000000000000000000000000000000000000000000000000000000000000) (46130519809315329731137/1000000000000000000000000) (23065259904657664865569/500000000000000000000000) { parts := 4, inner := (-6152561026237490700535486018575767656289602588685502988355019/8000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (231721905653207039316360668727/500000000000000000000000000000), innerHi := (92688762261282815726544267491/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell110
