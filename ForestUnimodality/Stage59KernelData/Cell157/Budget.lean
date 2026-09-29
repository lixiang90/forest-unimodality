import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell157.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell157
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(71482601952153977580796615173/500000000000000000000000000000)]
def alpha : ℚ := (6899417345112518540894941117/40000000000000000000000000000)
def D : ℚ := (149409862790909090909090909091/100000000000000000000000000000)
def mlo : ℚ := (43861846352485474499677211103937/2000000000000000000000000000000)
def mhi : ℚ := (13826016785022595222724338282763/500000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (1195537048264564258290752913852260621494489848438812050811822155118577335039947338150009/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1016495123283908341704773/100000000000000000000000)) (.exp (-3135358903701256000512900986496999714080504797700180294236101/1000000000000000000000000000000000000000000000000000000000000) (21742072203978394071769/500000000000000000000000) (43484144407956788143539/1000000000000000000000000) { parts := 4, inner := (-3135358903701256000512900986496999714080504797700180294236101/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (228324616395858766406624188467/500000000000000000000000000000), innerHi := (91329846558343506562649675387/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (5481824545847936956645906927771790402543050801935371030940149864632595078985120946223/15625000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1016495123283908341704773/100000000000000000000000)) (.exp (-988319654427569826248631832700159084871516724725973770162999/250000000000000000000000000000000000000000000000000000000000) (1199479771484059936303/62500000000000000000000) (19191676343744958980849/1000000000000000000000000) { parts := 4, inner := (-988319654427569826248631832700159084871516724725973770162999/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (7444031862966919200409195439/20000000000000000000000000000), innerHi := (372201593148345960020459771951/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell157
