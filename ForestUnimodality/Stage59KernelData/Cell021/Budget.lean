import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell021.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell021
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(136370484110528142694387943449/1000000000000000000000000000000)]
def alpha : ℚ := (876683197/3657656250)
def D : ℚ := (90810693/50000000)
def mlo : ℚ := (2295/128)
def mhi : ℚ := (3825/128)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (421905053256806537404992843291008172971317604927017211/340000000000000000000000000000000000000000000000000000)) (.mul (.rat (3876413260582490138972389/1000000000000000000000000)) (.exp (-62594052206732417496724066043091/25600000000000000000000000000000) (5419948927392642109451/62500000000000000000000) (86719182838282273751217/1000000000000000000000000) { parts := 3, inner := (-20864684068910805832241355347697/25600000000000000000000000000000), terms := 40, innerLo := (8852549991166855149025732329/20000000000000000000000000000), innerHi := (442627499558342757451286616451/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (990009828925539692135059072830651796163952814781051633/1020000000000000000000000000000000000000000000000000000)) (.mul (.rat (3876413260582490138972389/1000000000000000000000000)) (.exp (-20864684068910805832241355347697/5120000000000000000000000000000) (16989944546245235308873/1000000000000000000000000) (8494972273122617654437/500000000000000000000000) { parts := 5, inner := (-20864684068910805832241355347697/25600000000000000000000000000000), terms := 40, innerLo := (8852549991166855149025732329/20000000000000000000000000000), innerHi := (442627499558342757451286616451/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell021
