import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell102.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell102
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(13742747909404248752725814831/100000000000000000000000000000)]
def alpha : ℚ := (173379546821668794726007254191/1000000000000000000000000000000)
def D : ℚ := (1453200913123152709359605911331/1000000000000000000000000000000)
def mlo : ℚ := (4218673218673218673218673218673/250000000000000000000000000000)
def mhi : ℚ := (78417690417690417690417690417687/4000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (10469822337635582656271478704982371612667309585134924845489283061497694180832315173513/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (384668655796943648184083/625000000000000000000000)) (.exp (-57976162556381069062482123009399943232029638874351369539263/25000000000000000000000000000000000000000000000000000000000) (98367333933912228450737/1000000000000000000000000) (49183666966956114225369/500000000000000000000000) { parts := 3, inner := (-57976162556381069062482123009399943232029638874351369539263/75000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (5770236938585278625979929399/12500000000000000000000000000), innerHi := (461618955086822290078394351921/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (518564690644817818166250848949935026846864739768201586999815671203776020036409218279029/8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (384668655796943648184083/625000000000000000000000)) (.exp (-1077674551048024577867314757115913719502845254766547809315897/400000000000000000000000000000000000000000000000000000000000) (6759735812959413895309/100000000000000000000000) (67597358129594138953091/1000000000000000000000000) { parts := 3, inner := (-359224850349341525955771585705304573167615084922182603105299/400000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (2036791522325948720618095347/5000000000000000000000000000), innerHi := (407358304465189744123619069401/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell102
