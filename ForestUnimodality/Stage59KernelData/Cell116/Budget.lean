import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell116.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell116
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(140241769143476673945265095559/1000000000000000000000000000000)]
def alpha : ℚ := (43372334446878443675491299579/250000000000000000000000000000)
def D : ℚ := (370145866201923076923076923077/250000000000000000000000000000)
def mlo : ℚ := (8317127689298686784017882089969/500000000000000000000000000000)
def mhi : ℚ := (22015926236378876781223805532271/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (54769131621070795626331053135925552475007279174945885928994121111394567540409223601089/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2167614194911802183440841/500000000000000000000000)) (.exp (-1166408701339444021606232494971953034523912500876341420347671/500000000000000000000000000000000000000000000000000000000000) (776176092669460321579/8000000000000000000000) (189496116374379961323/1953125000000000000000) { parts := 3, inner := (-388802900446481340535410831657317678174637500292113806782557/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (459504841452337730311697959207/1000000000000000000000000000000), innerHi := (57438105181542216288962244901/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (107642618933269579099549453116184771337397137735807868252290377791572490477405021236723/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2167614194911802183440841/500000000000000000000000)) (.exp (-3087552444722057704251791898455186296300844087810779673284489/1000000000000000000000000000000000000000000000000000000000000) (45613459354881605427517/1000000000000000000000000) (22806729677440802713759/500000000000000000000000) { parts := 4, inner := (-3087552444722057704251791898455186296300844087810779673284489/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (115534918238365978000317791203/250000000000000000000000000000), innerHi := (462139672953463912001271164813/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell116
