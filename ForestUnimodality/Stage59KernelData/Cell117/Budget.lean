import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell117.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell117
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(140241769143476673945265095559/1000000000000000000000000000000)]
def alpha : ℚ := (43372334446878443675491299579/250000000000000000000000000000)
def D : ℚ := (370145866201923076923076923077/250000000000000000000000000000)
def mlo : ℚ := (22015926236378876781223805532271/1000000000000000000000000000000)
def mhi : ℚ := (6849399273540094998602961721151/250000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (6069213036838482336238780279928597222141060137347515572309821083836454467308937452991/15625000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3648786099433841023653713/500000000000000000000000)) (.exp (-3087552444722057704251791898455186296300844087810779673284489/1000000000000000000000000000000000000000000000000000000000000) (45613459354881605427517/1000000000000000000000000) (22806729677440802713759/500000000000000000000000) { parts := 4, inner := (-3087552444722057704251791898455186296300844087810779673284489/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (115534918238365978000317791203/250000000000000000000000000000), innerHi := (462139672953463912001271164813/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (3313356942631987549636837806585619807569311659944352530740630005203438992122705109927/15625000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3648786099433841023653713/500000000000000000000000)) (.exp (-960571871691306841322779701741616630888465793467219126468409/250000000000000000000000000000000000000000000000000000000000) (335070175113836594847/15625000000000000000000) (21444491207285542070209/1000000000000000000000000) { parts := 4, inner := (-960571871691306841322779701741616630888465793467219126468409/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (382673982971001460355539545661/1000000000000000000000000000000), innerHi := (191336991485500730177769772831/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell117
