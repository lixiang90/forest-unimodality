import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell024.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell024
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(7280472308793186035419719867/62500000000000000000000000000)]
def alpha : ℚ := (168743817219444444444444444444571/650250000000000000000000000000000)
def D : ℚ := (177911323/100000000)
def mlo : ℚ := (3425373134328358208955223880597/200000000000000000000000000000)
def mhi : ℚ := (28544776119402985074626865671641/1000000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (3347202080113534317961639665455945269505556624350778079188008327517795983771594009451009/2312000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9467277605217709890439437/1000000000000000000000000)) (.exp (-24938334251761734255654115066813324172055092639014396720599/12500000000000000000000000000000000000000000000000000000000) (8500286056207056385959/62500000000000000000000) (27200915379862580435069/200000000000000000000000) { parts := 2, inner := (-24938334251761734255654115066813324172055092639014396720599/25000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (73757596733980670602971849777/200000000000000000000000000000), innerHi := (184393991834951676507429624443/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (28939455497663905133725269981768238126312671780924951081868023081942800148902024488671993/57800000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9467277605217709890439437/1000000000000000000000000)) (.exp (-207819452098014452130450958890106181118919909867763026191747/62500000000000000000000000000000000000000000000000000000000) (17984258812172253005183/500000000000000000000000) (35968517624344506010367/1000000000000000000000000) { parts := 4, inner := (-207819452098014452130450958890106181118919909867763026191747/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (435492454721934535455889324761/1000000000000000000000000000000), innerHi := (217746227360967267727944662381/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell024
