import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell115.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell115
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(139810597704783401184319942191/1000000000000000000000000000000)]
def alpha : ℚ := (175470783620868896578239138793/1000000000000000000000000000000)
def D : ℚ := (1464643660914972802748353850559/1000000000000000000000000000000)
def mlo : ℚ := (22067307692307692307692307692307/1000000000000000000000000000000)
def mhi : ℚ := (13730769230769230769230769230769/500000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (36814973172484504438385845836357593047260614929745346818904444281559448139659954479173/100000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7036632406802072914331347/1000000000000000000000000)) (.exp (-3085243478196902939596291032003220515740050534568410855424637/1000000000000000000000000000000000000000000000000000000000000) (45718900989385437873633/1000000000000000000000000) (22859450494692718936817/500000000000000000000000) { parts := 4, inner := (-3085243478196902939596291032003220515740050534568410855424637/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (462406516221274872818975842191/1000000000000000000000000000000), innerHi := (28900407263829679551185990137/62500000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (19777384123201365289621217256776990085458169427464984986689501333429286601074005657019/100000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7036632406802072914331347/1000000000000000000000000)) (.exp (-1919707053100295162415469975468698505246683511522803618474879/500000000000000000000000000000000000000000000000000000000000) (2688274750329553281381/125000000000000000000000) (21506198002636426251049/1000000000000000000000000) { parts := 4, inner := (-1919707053100295162415469975468698505246683511522803618474879/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (191474486862313775754022384717/500000000000000000000000000000), innerHi := (76589794744925510301608953887/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell115
