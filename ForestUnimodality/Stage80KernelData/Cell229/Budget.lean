import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage80KernelData.Cell229.Parameters

namespace ForestUnimodality.Stage80KernelData.Cell229
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(181641863151369069165362535943/1000000000000000000000000000000)]
def R : ℚ := (4345673/2500000)
def D : ℚ := (1159225235469879518072289156627/500000000000000000000000000000)
def vmax : ℚ := (3569/15876)
def mlo : ℚ := (39/2)
def mhi : ℚ := (24/1)
def alpha : ℚ := (15509706937/39690000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.rat (7106777937745636432688678115200125613834512792133256527391859/22050000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (59558648358259400623637703/10000000000000000000000000)) (.exp (-7084032662903393697449138901777/2000000000000000000000000000000) (14477442768422899721409/500000000000000000000000) (28954885536845799442819/1000000000000000000000000) { parts := 4, inner := (-7084032662903393697449138901777/8000000000000000000000000000000), terms := 40, innerLo := (41250618356344358767572666433/100000000000000000000000000000), innerHi := (412506183563443587675726664331/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (362226172664394425210686776187086585679577907087173579030143/1378125000000000000000000000000000000000000000000000000000000)) (.mul (.rat (59558648358259400623637703/10000000000000000000000000)) (.exp (-544925589454107207496087607829/125000000000000000000000000000) (12785996688487089509651/1000000000000000000000000) (3196499172121772377413/250000000000000000000000) { parts := 5, inner := (-544925589454107207496087607829/625000000000000000000000000000), terms := 40, innerLo := (209082132930233460675867715903/500000000000000000000000000000), innerHi := (418164265860466921351735431807/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage80KernelData.Cell229
