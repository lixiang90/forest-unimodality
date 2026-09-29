import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell222.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell222
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(29988258768335105035531109167/500000000000000000000000000000)]
def alpha : ℚ := (165681000563785499960040976163/500000000000000000000000000000)
def D : ℚ := (1157460523940042826552462526767/500000000000000000000000000000)
def mlo : ℚ := (1866790254237288135593220338983/125000000000000000000000000000)
def mhi : ℚ := (4873305084745762711864406779661/200000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (4002659371002154723759607874267840761092806400603084515428109633510340573939480570063/625000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (661770237811913819570009/50000000000000000000000)) (.exp (-55981789210273875899221077467737617122435508384489718757161/62500000000000000000000000000000000000000000000000000000000) (204159075341320630681227/500000000000000000000000) (81663630136528252272491/200000000000000000000000) { parts := 1, inner := (-55981789210273875899221077467737617122435508384489718757161/62500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (51039768835330157670306866957/125000000000000000000000000000), innerHi := (408318150682641261362454935657/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (4069380507935574294012662705871019894043651235628054544768744877836780191313160190021/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (661770237811913819570009/50000000000000000000000)) (.exp (-146141933938399170768492918021044830707478502794829906252387/100000000000000000000000000000000000000000000000000000000000) (115953443225409270412589/500000000000000000000000) (231906886450818540825179/1000000000000000000000000) { parts := 2, inner := (-146141933938399170768492918021044830707478502794829906252387/200000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (60195889401138012427075512433/125000000000000000000000000000), innerHi := (96313423041820819883320819893/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell222
