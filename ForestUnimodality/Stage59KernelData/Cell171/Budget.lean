import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell171.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell171
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(100671017038518644606298855117/1000000000000000000000000000000)]
def alpha : ℚ := (173477484006594836993902481751/1000000000000000000000000000000)
def D : ℚ := (1507003964492032394262904797327/1000000000000000000000000000000)
def mlo : ℚ := (8513396317321993422292980287827/500000000000000000000000000000)
def mhi : ℚ := (27432054800259756582944047594109/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (75792314538103817819727188192817756711554064780942097462490201887692910575012381077/40000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1013963637048728649858731/100000000000000000000000)) (.exp (-857052265716784281429044135889750428845264400043359231760759/500000000000000000000000000000000000000000000000000000000000) (90062472371430452600633/500000000000000000000000) (180124944742860905201267/1000000000000000000000000) { parts := 2, inner := (-857052265716784281429044135889750428845264400043359231760759/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (106102822989912980802487190637/250000000000000000000000000000), innerHi := (424411291959651923209948762549/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (56730217104603236865226533798913549413989641187554939571493242158162159817575416859/80000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1013963637048728649858731/100000000000000000000000)) (.exp (-2761612856198527129049142215644729010497621173774245013705753/1000000000000000000000000000000000000000000000000000000000000) (63189770115087327835059/1000000000000000000000000) (3159488505754366391753/50000000000000000000000) { parts := 3, inner := (-920537618732842376349714071881576336832540391258081671235251/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (199152423682534938089989573471/500000000000000000000000000000), innerHi := (398304847365069876179979146943/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell171
