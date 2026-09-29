import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell226.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell226
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(31260542780823687412379331221/500000000000000000000000000000)]
def alpha : ℚ := (77256408888888888888888888889/200000000000000000000000000000)
def D : ℚ := (1159225235469879518072289156627/500000000000000000000000000000)
def mlo : ℚ := (15/1)
def mhi : ℚ := (24/1)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (140943044332004609320427954344085932093404823420427292919/50000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4646095790122548585543427/1000000000000000000000000)) (.exp (-93781628342471062237137993663/100000000000000000000000000000) (391481787893167358457693/1000000000000000000000000) (195740893946583679228847/500000000000000000000000) { parts := 1, inner := (-93781628342471062237137993663/100000000000000000000000000000), terms := 40, innerLo := (19574089394658367922884660241/50000000000000000000000000000), innerHi := (391481787893167358457693204821/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (276038887998748911749308209307184042468564631491157854101/125000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4646095790122548585543427/1000000000000000000000000)) (.exp (-93781628342471062237137993663/62500000000000000000000000000) (223017272920393449129183/1000000000000000000000000) (6969289778762295285287/31250000000000000000000) { parts := 2, inner := (-93781628342471062237137993663/125000000000000000000000000000), terms := 40, innerLo := (472247046491974843276356385733/1000000000000000000000000000000), innerHi := (236123523245987421638178192867/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell226
