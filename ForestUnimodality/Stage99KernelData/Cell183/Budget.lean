import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage99KernelData.Cell183.Parameters

namespace ForestUnimodality.Stage99KernelData.Cell183
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(181576817074448272638346562523/1000000000000000000000000000000)]
def R : ℚ := (5095673/2500000)
def D : ℚ := (1159225235469879518072289156627/500000000000000000000000000000)
def vmax : ℚ := (3569/15876)
def mlo : ℚ := (24/1)
def mhi : ℚ := (63/2)
def alpha : ℚ := (18186456937/39690000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.rat (425708005723357871159418799096092412691674569019826333464733/1653750000000000000000000000000000000000000000000000000000000)) (.mul (.rat (65027664644586256059710649/10000000000000000000000000)) (.exp (-544730451223344817915039687569/125000000000000000000000000000) (12805972570842199148093/1000000000000000000000000) (6402986285421099574047/500000000000000000000000) { parts := 5, inner := (-544730451223344817915039687569/625000000000000000000000000000), terms := 40, innerLo := (104573711495089477940514895897/250000000000000000000000000000), innerHi := (418294845980357911762059583589/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (249087550250637832981807365079842412691674569019826333464733/1260000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (65027664644586256059710649/10000000000000000000000000)) (.exp (-11439339475690241176215833438949/2000000000000000000000000000000) (131231769824694268191/40000000000000000000000) (410099280702169588097/125000000000000000000000) { parts := 6, inner := (-3813113158563413725405277812983/4000000000000000000000000000000), terms := 40, innerLo := (94110168526069330263262971/244140625000000000000000000), innerHi := (385475250282779976758325129217/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

theorem budget_hi_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms (∅ : Finset ℤ)
    row.A row.B row.dδ row.dM alpha varianceIntercept D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ)) (fun _ => 0) (fun _ => 0)
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage99KernelData.Cell183
