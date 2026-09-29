import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell002.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell002
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(38264964868187752565882634817/500000000000000000000000000000)]
def alpha : ℚ := (633353828000000000000000000000247/2450000000000000000000000000000000)
def D : ℚ := (76410016897506925207756232687/50000000000000000000000000000)
def mlo : ℚ := (3453947368421052631578947368421/125000000000000000000000000000)
def mhi : ℚ := (46052631578947368421052631578947/1000000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (25749498535644787987758265234092220851731644331308290464979022010842181524106414772111093/15312500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1412042810399618986139103/250000000000000000000000)) (.exp (-132165174709201119059791995256083512370270095381443900913957/62500000000000000000000000000000000000000000000000000000000) (30169097005623928505329/250000000000000000000000) (120676388022495714021317/1000000000000000000000000) { parts := 3, inner := (-132165174709201119059791995256083512370270095381443900913957/187500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (98833482077212668213731759623/200000000000000000000000000000), innerHi := (123541852596515835267164699529/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (81651284063083650774303105663191244293896334067173912288646385827843878264549013491595213/70000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1412042810399618986139103/250000000000000000000000)) (.exp (-1762202329456014920797226603414459586591890667670107306397699/500000000000000000000000000000000000000000000000000000000000) (29469346460501943408209/1000000000000000000000000) (2946934646050194340821/100000000000000000000000) { parts := 4, inner := (-1762202329456014920797226603414459586591890667670107306397699/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (414326418752540629071842067709/1000000000000000000000000000000), innerHi := (41432641875254062907184206771/100000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
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
    row.A row.B row.dδ row.dM alpha 0 D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell002
