import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell220.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell220
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(58643943207074338458157139587/1000000000000000000000000000000)]
def alpha : ℚ := (315950224741901032395870416519/1000000000000000000000000000000)
def D : ℚ := (1170408068682170542635658914729/500000000000000000000000000000)
def mlo : ℚ := (610303030303030303030303030303/40000000000000000000000000000)
def mhi : ℚ := (24893939393939393939393939393939/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (1438935811396797332682216588345834521836335648696738222794395997842578830456661638283/200000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (23682642058752922942233/1562500000000000000000)) (.exp (-35790576248196278077190448220670344122933118959440661904861/40000000000000000000000000000000000000000000000000000000000) (20435193769818695164959/50000000000000000000000) (408703875396373903299181/1000000000000000000000000) { parts := 1, inner := (-35790576248196278077190448220670344122933118959440661904861/40000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (204351937698186951649590347209/500000000000000000000000000000), innerHi := (408703875396373903299180694419/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (22602028215965489212265549476172589980496366037147317978887147971953524795936601297679/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (23682642058752922942233/1562500000000000000000)) (.exp (-1459878768018532395253820914264234473598130546472728604763193/1000000000000000000000000000000000000000000000000000000000000) (9290577236007705842491/40000000000000000000000) (58066107725048161515569/250000000000000000000000) { parts := 2, inner := (-1459878768018532395253820914264234473598130546472728604763193/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (481938202366436858981351308331/1000000000000000000000000000000), innerHi := (120484550591609214745337827083/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell220
