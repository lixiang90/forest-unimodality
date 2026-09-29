import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell168.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell168
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(20118294355910764812514375709/200000000000000000000000000000)]
def alpha : ℚ := (174412830036003106926376454329/1000000000000000000000000000000)
def D : ℚ := (749379404798408095006244840069/500000000000000000000000000000)
def mlo : ℚ := (2130027618170851718993047839751/125000000000000000000000000000)
def mhi : ℚ := (27453689300868755489243727712347/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (2247146427517848092289867705044941438473216543763952951668430608354141784984923885601/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (602990493522411630245017/62500000000000000000000)) (.exp (-42852522608580695768073698654722281086773743390454839008459/25000000000000000000000000000000000000000000000000000000000) (180125598073492950837783/1000000000000000000000000) (22515699759186618854723/125000000000000000000000) { parts := 2, inner := (-42852522608580695768073698654722281086773743390454839008459/50000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (106103015412349659702550471139/250000000000000000000000000000), innerHi := (424412061649398638810201884557/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (6695416227982233707945165741307873209006132704005528241458734137314716618941733434797/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (602990493522411630245017/62500000000000000000000)) (.exp (-552321402510595634344061004883102826014027289849605436179023/200000000000000000000000000000000000000000000000000000000000) (31595069687392555422921/500000000000000000000000) (63190139374785110845843/1000000000000000000000000) { parts := 3, inner := (-184107134170198544781353668294367608671342429949868478726341/200000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (398305623216608320505821650599/1000000000000000000000000000000), innerHi := (1991528116083041602529108253/5000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell168
