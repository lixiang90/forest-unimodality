import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell072.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell072
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(23583638158447074819725156197/250000000000000000000000000000)]
def alpha : ℚ := (6320165846404933903673469387759077/34151040000000000000000000000000000)
def D : ℚ := (1627341600829809503872723466611/1000000000000000000000000000000)
def mlo : ℚ := (17218290009395552771688067647979/1000000000000000000000000000000)
def mhi : ℚ := (73937362981522079549013466958969/4000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (16434907938184898363287548850849915537037627670022540855955865134066703218289789896006980541/13340250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (311004432031181821116661/50000000000000000000000)) (.exp (-406069921288789000763811349013026620467492095546688186375863/250000000000000000000000000000000000000000000000000000000000) (197053564703388040809311/1000000000000000000000000) (6157923896980876275291/31250000000000000000000) { parts := 2, inner := (-406069921288789000763811349013026620467492095546688186375863/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (443907157751920058864840372167/1000000000000000000000000000000), innerHi := (55488394718990007358105046521/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (4670136482799246597631335082793612810946654480095581942433479096213170104953951455248367822989/4268880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (311004432031181821116661/50000000000000000000000)) (.exp (-1743712014945976297397542851644181458585639626903362115080893/1000000000000000000000000000000000000000000000000000000000000) (174870074024339004880907/1000000000000000000000000) (43717518506084751220227/250000000000000000000000) { parts := 2, inner := (-1743712014945976297397542851644181458585639626903362115080893/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (209087346594873481407029653651/500000000000000000000000000000), innerHi := (418174693189746962814059307303/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell072
