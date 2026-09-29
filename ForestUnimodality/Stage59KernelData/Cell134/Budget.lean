import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell134.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell134
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(98226430340691151097279725601/1000000000000000000000000000000)]
def alpha : ℚ := (85575984641436403392482836039/500000000000000000000000000000)
def D : ℚ := (294812646178106907230375656389/200000000000000000000000000000)
def mlo : ℚ := (8203532681789653008159239666457/500000000000000000000000000000)
def mhi : ℚ := (5428808392360799784811261543979/250000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (103412744364603982800844051428495595055242320932056640527462748350713687374945705035287/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1977851080697783814343893/500000000000000000000000)) (.exp (-805803731515394618353314015434178705994826470872731723865657/500000000000000000000000000000000000000000000000000000000000) (19956656023542707730053/100000000000000000000000) (199566560235427077300531/1000000000000000000000000) { parts := 2, inner := (-805803731515394618353314015434178705994826470872731723865657/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (446728732269849727538580558789/1000000000000000000000000000000), innerHi := (44672873226984972753858055879/100000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (31659265655895796515441631871237227805382515997104573941573756476948411371797309907931/62500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1977851080697783814343893/500000000000000000000000)) (.exp (-533252469385187615086751921978510725805582000401920713706379/250000000000000000000000000000000000000000000000000000000000) (59240072953029314226419/500000000000000000000000) (118480145906058628452839/1000000000000000000000000) { parts := 3, inner := (-533252469385187615086751921978510725805582000401920713706379/750000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (491151181879082565863213887847/1000000000000000000000000000000), innerHi := (61393897734885320732901735981/125000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell134
