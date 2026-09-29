import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell180.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell180
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(50512583662961912226586616731/500000000000000000000000000000)]
def alpha : ℚ := (87273152202530289256650507177/500000000000000000000000000000)
def D : ℚ := (18822645312049250580094905617/12500000000000000000000000000)
def mlo : ℚ := (8493380286105392950814533067221/500000000000000000000000000000)
def mhi : ℚ := (27367558699672932841513495438823/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (4972444566704388667463871329349969019574959466460234971043578467472031480522128222223/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (529366757065965032325039/50000000000000000000000)) (.exp (-429022582283250043919658666985963938693420424919130586274551/250000000000000000000000000000000000000000000000000000000000) (179767607958688843149601/1000000000000000000000000) (89883803979344421574801/500000000000000000000000) { parts := 2, inner := (-429022582283250043919658666985963938693420424919130586274551/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (211995051804687674383205673503/500000000000000000000000000000), innerHi := (423990103609375348766411347007/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (3762961063184999328890488576130442082925403495489315922142460431900502411998251915749/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (529366757065965032325039/50000000000000000000000)) (.exp (-1382406098468250141518900149176983688549096266536703758747613/500000000000000000000000000000000000000000000000000000000000) (6298792756305264744109/100000000000000000000000) (62987927563052647441091/1000000000000000000000000) { parts := 3, inner := (-1382406098468250141518900149176983688549096266536703758747613/1500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (4973503785095669920228467879/12500000000000000000000000000), innerHi := (397880302807653593618277430321/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell180
