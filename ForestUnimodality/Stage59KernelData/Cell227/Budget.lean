import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell227.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell227
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(3108984815985449218926151757/50000000000000000000000000000)]
def alpha : ℚ := (49288861316568047337278106509/125000000000000000000000000000)
def D : ℚ := (278865343/100000000)
def mlo : ℚ := (7428571428571428571428571428571/500000000000000000000000000000)
def mhi : ℚ := (5942857142857142857142857142857/250000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (494016829709999504689005797336209183201667842066941729854270699826388928071482997881741/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7436062571100334750440197/1000000000000000000000000)) (.exp (-23095315775891908483451413051998667577936006236049031649247/25000000000000000000000000000000000000000000000000000000000) (198501263904988955585799/500000000000000000000000) (397002527809977911171599/1000000000000000000000000) { parts := 1, inner := (-23095315775891908483451413051998667577936006236049031649247/25000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (397002527809977911171598242119/1000000000000000000000000000000), innerHi := (9925063195249447779289956053/25000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (84248311858900865476507969768191000733182179516227154446537633655049346595924215802249/31250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7436062571100334750440197/1000000000000000000000000)) (.exp (-18476252620713526786761130441599555859312002078683010549749/12500000000000000000000000000000000000000000000000000000000) (57017640830376786742981/250000000000000000000000) (9122822532860285878877/40000000000000000000000) { parts := 2, inner := (-18476252620713526786761130441599555859312002078683010549749/25000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (238783669521968747935039123833/500000000000000000000000000000), innerHi := (477567339043937495870078247667/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell227
