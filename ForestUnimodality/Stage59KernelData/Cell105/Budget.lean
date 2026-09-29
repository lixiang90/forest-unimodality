import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell105.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell105
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(68966644910026848797033865263/500000000000000000000000000000)]
def alpha : ℚ := (174430479525700519556906185669/1000000000000000000000000000000)
def D : ℚ := (1452087397366093366093366093367/1000000000000000000000000000000)
def mlo : ℚ := (16833333333333333333333333333333/1000000000000000000000000000000)
def mhi : ℚ := (39112745098039215686274509803921/2000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (1191891956432179514997419683648414819358300410955948543983292202201425014887514068377/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9627653608600262868932873/10000000000000000000000000)) (.exp (-1160938522652118621416736731927143677785029991050400988711579/500000000000000000000000000000000000000000000000000000000000) (49044647323659708012041/500000000000000000000000) (98089294647319416024083/1000000000000000000000000) { parts := 3, inner := (-386979507550706207138912243975714559261676663683466996237193/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (461183616385072199629622146471/1000000000000000000000000000000), innerHi := (57647952048134024953702768309/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (35847581950324018615932191201039941561493255494238319014668569816811319637105123655307/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9627653608600262868932873/10000000000000000000000000)) (.exp (-2697474802632863855644770641830730391515639396497742863096223/1000000000000000000000000000000000000000000000000000000000000) (33687717188058890001437/500000000000000000000000) (539003475008942240023/8000000000000000000000) { parts := 3, inner := (-2697474802632863855644770641830730391515639396497742863096223/3000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (40691202668918247010324959677/100000000000000000000000000000), innerHi := (406912026689182470103249596771/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell105
