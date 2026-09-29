import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell063.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell063
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(11678828403853685031638690021/125000000000000000000000000000)]
def alpha : ℚ := (55507775195763/300125000000000)
def D : ℚ := (1632339656356627543878539894477/1000000000000000000000000000000)
def mlo : ℚ := (8677083333333333333333333333333/500000000000000000000000000000)
def mhi : ℚ := (39812499999999999999999999999999/2000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (13385979574139109024442769496892397065868800989598566732447310508988663985540256060846037053/12005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5622130689500462352725663/1000000000000000000000000)) (.exp (-101338167295938746159948216536381523723865382104989453769993/62500000000000000000000000000000000000000000000000000000000) (4940493120261214078727/25000000000000000000000) (197619724810448563149081/1000000000000000000000000) { parts := 2, inner := (-101338167295938746159948216536381523723865382104989453769993/125000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (222272200696830598477221428741/500000000000000000000000000000), innerHi := (444544401393661196954442857483/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (84450848256616198579434288415667685395708750979126791409063120288335473986467590261471193689/96040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5622130689500462352725663/1000000000000000000000000)) (.exp (-464963355828424835322115346461050821171596146314968361309979/250000000000000000000000000000000000000000000000000000000000) (38923862504669472679319/250000000000000000000000) (155695450018677890717277/1000000000000000000000000) { parts := 2, inner := (-464963355828424835322115346461050821171596146314968361309979/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (7891652552379074189046168103/20000000000000000000000000000), innerHi := (394582627618953709452308405151/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell063
