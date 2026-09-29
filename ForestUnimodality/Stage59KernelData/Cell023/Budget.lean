import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell023.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell023
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(14203834370183268091371285439/125000000000000000000000000000)]
def alpha : ℚ := (328783838900000000000000000000143/1300500000000000000000000000000000)
def D : ℚ := (358219917476923076923076923077/200000000000000000000000000000)
def mlo : ℚ := (17386363636363636363636363636363/1000000000000000000000000000000)
def mhi : ℚ := (3622159090909090909090909090909/125000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (887722244380869713245353608166638854451805095179205460604430936182981534703762925385044379/650250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1390340147770720591324789/200000000000000000000000)) (.exp (-246953029390686365679523485473513688469037156102123672818357/125000000000000000000000000000000000000000000000000000000000) (69337359793847188803817/500000000000000000000000) (27734943917538875521527/200000000000000000000000) { parts := 2, inner := (-246953029390686365679523485473513688469037156102123672818357/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (372390547124513322557743320111/1000000000000000000000000000000), innerHi := (23274409195282082659858957507/62500000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (214404914966618696189184889762474917782340002173044736382062180165929342031169425992539017/325125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1390340147770720591324789/200000000000000000000000)) (.exp (-51448547789726326183234059473649276924148165157446238974051/15625000000000000000000000000000000000000000000000000000000) (18576568711536889775947/500000000000000000000000) (7430627484614755910379/200000000000000000000000) { parts := 4, inner := (-51448547789726326183234059473649276924148165157446238974051/62500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (439034726831570384404244862229/1000000000000000000000000000000), innerHi := (43903472683157038440424486223/100000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
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
    row.A row.B row.dδ row.dM alpha 0 D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell023
