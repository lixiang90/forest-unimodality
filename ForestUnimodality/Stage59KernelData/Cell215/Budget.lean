import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell215.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell215
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(56853991972543197712623203151/1000000000000000000000000000000)]
def alpha : ℚ := (275727910308641975308641975309/1000000000000000000000000000000)
def D : ℚ := (62906666332547169811320754717/31250000000000000000000000000)
def mlo : ℚ := (15981308411214953271028037383177/1000000000000000000000000000000)
def mhi : ℚ := (630841121495327102803738317757/25000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (41147905251525591465528073085779263004382105601363594973055948338120789082356151114129/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1834033076109921012175619/100000000000000000000000)) (.exp (-908601180121952038211081097086042354266258643597565700790727/1000000000000000000000000000000000000000000000000000000000000) (403087676912278003853309/1000000000000000000000000) (40308767691227800385331/100000000000000000000000) { parts := 1, inner := (-908601180121952038211081097086042354266258643597565700790727/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (80617535382455600770661979569/200000000000000000000000000000), innerHi := (201543838456139001926654948923/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (650691919779689667332671118102771943756223143921915740869769644887226050530428706789/125000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1834033076109921012175619/100000000000000000000000)) (.exp (-35865836057445475192542674884976104168299322026189601652307/25000000000000000000000000000000000000000000000000000000000) (238202663034460801994547/1000000000000000000000000) (59550665758615200498637/250000000000000000000000) { parts := 2, inner := (-35865836057445475192542674884976104168299322026189601652307/50000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (488060101867035226305865319061/1000000000000000000000000000000), innerHi := (244030050933517613152932659531/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell215
