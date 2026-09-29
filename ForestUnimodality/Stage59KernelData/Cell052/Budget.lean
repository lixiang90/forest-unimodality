import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell052.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell052
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(4607439105964959032803388371/50000000000000000000000000000)]
def alpha : ℚ := (42605988215071288128387713891/250000000000000000000000000000)
def D : ℚ := (819629440291587954217135237249/500000000000000000000000000000)
def mlo : ℚ := (4385638297872340425531914893617/250000000000000000000000000000)
def mhi : ℚ := (22702127659574468085106382978723/1000000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (908808993152332151695875089976236881720779440265779886706644991985574003899020875773/625000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7173253656007856804421863/1000000000000000000000000)) (.exp (-20206561398234620864608477190901497714061575213637599927907/12500000000000000000000000000000000000000000000000000000000) (49646902706797984307241/250000000000000000000000) (39717522165438387445793/200000000000000000000000) { parts := 2, inner := (-20206561398234620864608477190901497714061575213637599927907/25000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (222815849316869701685436767211/500000000000000000000000000000), innerHi := (445631698633739403370873534423/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (2287662794684282336677635281739155231292935543751494726801254847725906074081396639687/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7173253656007856804421863/1000000000000000000000000)) (.exp (-104598670767332155063855646635253456567169929059114398630233/50000000000000000000000000000000000000000000000000000000000) (12344329040872153335241/100000000000000000000000) (123443290408721533352411/1000000000000000000000000) { parts := 3, inner := (-104598670767332155063855646635253456567169929059114398630233/150000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (248957855380648964107516268787/500000000000000000000000000000), innerHi := (19916628430451917128601301503/40000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell052
