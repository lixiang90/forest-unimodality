import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell178.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell178
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(50444694675635651567339170879/500000000000000000000000000000)]
def alpha : ℚ := (174308520561964853994680430721/1000000000000000000000000000000)
def D : ℚ := (1506076104396385844557851585377/1000000000000000000000000000000)
def mlo : ℚ := (4248910077470752438603644575479/250000000000000000000000000000)
def mhi : ℚ := (27381864943700404604334598375309/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (2487187413044698669628593748027466108763607423350967641739654723397239521499713374693/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (106076696326823043392551/10000000000000000000000)) (.exp (-214334971562243529358100015702293338042031867788861794276041/125000000000000000000000000000000000000000000000000000000000) (180021359274089736371139/1000000000000000000000000) (9001067963704486818557/50000000000000000000000) { parts := 2, inner := (-214334971562243529358100015702293338042031867788861794276041/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (424289240111141324676048236217/1000000000000000000000000000000), innerHi := (212144620055570662338024118109/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (3749090512316308199526691153373665011236139830296194732285729809666870404627953915303/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (106076696326823043392551/10000000000000000000000)) (.exp (-1381269816734458300307755656748107017971463632900268525426611/500000000000000000000000000000000000000000000000000000000000) (31565617200698888986683/500000000000000000000000) (63131234401397777973367/1000000000000000000000000) { parts := 3, inner := (-1381269816734458300307755656748107017971463632900268525426611/1500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (79636363948568198595764940217/200000000000000000000000000000), innerHi := (199090909871420496489412350543/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell178
