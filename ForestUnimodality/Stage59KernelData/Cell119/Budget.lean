import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell119.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell119
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(140574066169765005120358225771/1000000000000000000000000000000)]
def alpha : ℚ := (43625670979391076841172299393/250000000000000000000000000000)
def D : ℚ := (2311663243198169879854708019/1562500000000000000000000000)
def mlo : ℚ := (10982391748745586322244935885523/500000000000000000000000000000)
def mhi : ℚ := (6833488199219475933841293439881/250000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (9716830749515542690999946892045611899440299037137701551890116716037348376173632993747/25000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7228099076133578826386383/1000000000000000000000000)) (.exp (-1543839464390443260331531276662210582961017075486197044413233/500000000000000000000000000000000000000000000000000000000000) (22803845172128403769409/500000000000000000000000) (45607690344256807538819/1000000000000000000000000) { parts := 4, inner := (-1543839464390443260331531276662210582961017075486197044413233/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (462125059859110321383268232707/1000000000000000000000000000000), innerHi := (115531264964777580345817058177/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (1337467729469585927076581329287322484723171815100707604842405816720747312343750959823/6250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7228099076133578826386383/1000000000000000000000000)) (.exp (-960611222287386917539619461034267486599436619524858613373251/250000000000000000000000000000000000000000000000000000000000) (21441116058874151625443/1000000000000000000000000) (5360279014718537906361/250000000000000000000000) { parts := 4, inner := (-960611222287386917539619461034267486599436619524858613373251/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (95664731204485701741204854871/250000000000000000000000000000), innerHi := (76531784963588561392963883897/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell119
