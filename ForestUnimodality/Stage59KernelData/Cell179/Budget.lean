import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell179.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell179
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(100965645181672685162168902061/1000000000000000000000000000000)]
def alpha : ℚ := (174427393326441842939476530573/1000000000000000000000000000000)
def D : ℚ := (376485957529090738010852178277/250000000000000000000000000000)
def mlo : ℚ := (8495599640445680122081234191107/500000000000000000000000000000)
def mhi : ℚ := (6843677488136797876120994209503/250000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (4977187317465111376167569815716771980582662310739999711602864681432211060263285213249/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (530306909359015232752199/50000000000000000000000)) (.exp (-857763698902784579732133922971699436735538003318635640171527/500000000000000000000000000000000000000000000000000000000000) (89934416632820605541823/500000000000000000000000) (179868833265641211083647/1000000000000000000000000) { parts := 2, inner := (-857763698902784579732133922971699436735538003318635640171527/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (424109459061739403553169168203/1000000000000000000000000000000), innerHi := (106027364765434850888292292051/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (939782571136568884557291990470810758778278954350035444208101370796018349120803956021/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (530306909359015232752199/50000000000000000000000)) (.exp (-690976313005020911450885660171660791487680846101840122485683/250000000000000000000000000000000000000000000000000000000000) (31522540028457950720211/500000000000000000000000) (63045080056915901440423/1000000000000000000000000) { parts := 3, inner := (-230325437668340303816961886723886930495893615367280040828561/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (49750075770518522222213627223/125000000000000000000000000000), innerHi := (79600121232829635555541803557/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell179
