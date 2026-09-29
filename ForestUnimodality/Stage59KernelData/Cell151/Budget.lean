import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell151.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell151
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(71371051852287671986882085061/500000000000000000000000000000)]
def alpha : ℚ := (86181024171924770708020699027/500000000000000000000000000000)
def D : ℚ := (1487060243217543094043203142047/1000000000000000000000000000000)
def mlo : ℚ := (22002397558849171752397558849171/1000000000000000000000000000000)
def mhi : ℚ := (13871076721883173496076721883173/500000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (283188299265625822704115792335456620543901502310901025743355068702052877965995884183551/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9914588637146270144739901/1000000000000000000000000)) (.exp (-1570334257047271932009543557247715916985397973617328091334431/500000000000000000000000000000000000000000000000000000000000) (8650774482228711279389/200000000000000000000000) (21626936205571778198473/500000000000000000000000) { parts := 4, inner := (-1570334257047271932009543557247715916985397973617328091334431/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (456043477543078511507676839007/1000000000000000000000000000000), innerHi := (14251358673221203484614901219/31250000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (163270110555790496457196964021120534978337536725736893263470023672871286902478548626201/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (9914588637146270144739901/1000000000000000000000000)) (.exp (-989993335964584478875581807830080222207058455374576690578553/250000000000000000000000000000000000000000000000000000000000) (3812724489491884022023/200000000000000000000000) (4765905611864855027529/250000000000000000000000) { parts := 4, inner := (-989993335964584478875581807830080222207058455374576690578553/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (371579167230525004931516456473/1000000000000000000000000000000), innerHi := (185789583615262502465758228237/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell151
