import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell008.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell008
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(28540061780381397000539871871/250000000000000000000000000000)]
def alpha : ℚ := (2246497914285714285714285714287/7087500000000000000000000000000)
def D : ℚ := (6663680383/4000000000)
def mlo : ℚ := (189/8)
def mhi : ℚ := (315/8)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (15111474386081241677577460529827651984293815782056850853/10000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7583240340007712632086623/1000000000000000000000000)) (.exp (-5394071676492084033102035783619/2000000000000000000000000000000) (33702508142291345963941/500000000000000000000000) (67405016284582691927883/1000000000000000000000000) { parts := 3, inner := (-1798023892164028011034011927873/2000000000000000000000000000000), terms := 40, innerLo := (101742892752036039955213191461/250000000000000000000000000000), innerHi := (81394314201628831964170553169/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (10848822398057640921391529013360847317026102494750350101/6000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7583240340007712632086623/1000000000000000000000000)) (.exp (-1798023892164028011034011927873/400000000000000000000000000000) (2791003441020414896557/250000000000000000000000) (11164013764081659586229/1000000000000000000000000) { parts := 5, inner := (-1798023892164028011034011927873/2000000000000000000000000000000), terms := 40, innerLo := (101742892752036039955213191461/250000000000000000000000000000), innerHi := (81394314201628831964170553169/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell008
