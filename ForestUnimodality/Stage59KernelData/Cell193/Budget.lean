import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell193.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell193
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(20164932660356614379975610151/200000000000000000000000000000)]
def alpha : ℚ := (182112166481890260631001371743/1000000000000000000000000000000)
def D : ℚ := (154417175278947368421052631579/100000000000000000000000000000)
def mlo : ℚ := (670344827586206896551724137931/40000000000000000000000000000)
def mhi : ℚ := (27/1)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (145079113732876724880650378238260741389541532536481409281618514745470544094084026066961/80000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9439749421434004972297771/1000000000000000000000000)) (.exp (-13517458307494227018852615908117925347149642875366207737581/8000000000000000000000000000000000000000000000000000000000) (184578157293147508124249/1000000000000000000000000) (738312629172590032497/4000000000000000000000) { parts := 2, inner := (-13517458307494227018852615908117925347149642875366207737581/16000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (214812800650442796257919782563/500000000000000000000000000000), innerHi := (429625601300885592515839565127/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (691551102688545224569841304916311332679671696080182227971/1000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9439749421434004972297771/1000000000000000000000000)) (.exp (-544453181829628588259341474077/200000000000000000000000000000) (6572565720189203087443/100000000000000000000000) (65725657201892030874431/1000000000000000000000000) { parts := 3, inner := (-181484393943209529419780491359/200000000000000000000000000000), terms := 40, innerLo := (50445410307472235367174872787/125000000000000000000000000000), innerHi := (403563282459777882937398982297/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell193
