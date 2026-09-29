import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell081.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell081
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(23728479137628599089374530441/250000000000000000000000000000)]
def alpha : ℚ := (3208094561038348000000000000003799/17424000000000000000000000000000000)
def D : ℚ := (64963022300408163265306122449/40000000000000000000000000000)
def mlo : ℚ := (74061068702290076335877862595419/4000000000000000000000000000000)
def mhi : ℚ := (7960305343511450381679389312977/400000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (90023526483015303064163162686402825611365315720701294004612488849042998510398079456320403/77440000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6692502154745162634696953/1000000000000000000000000)) (.exp (-1757356523612768460802379346096025695716150558973290682649779/1000000000000000000000000000000000000000000000000000000000000) (172500262010096073065969/1000000000000000000000000) (17250026201009607306597/100000000000000000000000) { parts := 2, inner := (-1757356523612768460802379346096025695716150558973290682649779/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (25958219285554581072617603449/62500000000000000000000000000), innerHi := (83066301713774659432376331037/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (23702164184571003296270547934592680057450577963043222928607782568582675152302027917085547/23232000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6692502154745162634696953/1000000000000000000000000)) (.exp (-188885939272664909392364582777667874273062678077952962832857/100000000000000000000000000000000000000000000000000000000000) (151244220748776430365793/1000000000000000000000000) (75622110374388215182897/500000000000000000000000) { parts := 2, inner := (-188885939272664909392364582777667874273062678077952962832857/200000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (388901299494841531913891687059/1000000000000000000000000000000), innerHi := (19445064974742076595694584353/50000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell081
