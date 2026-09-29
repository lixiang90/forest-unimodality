import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell139.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell139
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(276316064746884524548519503/1953125000000000000000000000)]
def alpha : ℚ := (17213858631316863905325443787/100000000000000000000000000000)
def D : ℚ := (11507826440637454659442031257/7812500000000000000000000000)
def mlo : ℚ := (8859259259259259259259259259259/400000000000000000000000000000)
def mhi : ℚ := (1117037037037037037037037037037/40000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (349034172368361574479253060162598385791308383318962380282283096347535231913661156428247/800000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7583900159092371140445721/1000000000000000000000000)) (.exp (-2447955655090917713777995004355483918057287844752894828277/781250000000000000000000000000000000000000000000000000000) (10892534859720145093933/250000000000000000000000) (43570139438880580375733/1000000000000000000000000) { parts := 4, inner := (-2447955655090917713777995004355483918057287844752894828277/3125000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (91374966999833373639725663197/200000000000000000000000000000), innerHi := (228437417499583434099314157993/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (10070876196287336195702198050750126965186965743186537749749157068042086486189258440443/40000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7583900159092371140445721/1000000000000000000000000)) (.exp (-308655278250593972606790674462211988293898263536127832611/78125000000000000000000000000000000000000000000000000000) (9619771740665751499651/500000000000000000000000) (19239543481331502999303/1000000000000000000000000) { parts := 4, inner := (-308655278250593972606790674462211988293898263536127832611/312500000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (93108364775562276054403949941/250000000000000000000000000000), innerHi := (74486691820449820843523159953/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell139
