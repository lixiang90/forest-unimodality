import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell077.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell077
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(18927750485838141648292117761/200000000000000000000000000000)]
def alpha : ℚ := (57025217481449/306281250000000)
def D : ℚ := (325140863437269025994362668337/200000000000000000000000000000)
def mlo : ℚ := (74249999999999999999999999999999/4000000000000000000000000000000)
def mhi : ℚ := (1596122448979591836734693877551/80000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (174397771471095307736356747342005631934171488308841164062481736754941/153140625000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6580148685501957750432211/1000000000000000000000000)) (.exp (-1405385473573482017385689743754231072249514161858351707882239/800000000000000000000000000000000000000000000000000000000000) (172608053421842461946449/1000000000000000000000000) (3452161068436849238929/20000000000000000000000) { parts := 2, inner := (-1405385473573482017385689743754231072249514161858351707882239/1600000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (207730626907686906654574942601/500000000000000000000000000000), innerHi := (415461253815373813309149885203/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (3059441127162691965404377287262427872784644844716976337985851770509/3062812500000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6580148685501957750432211/1000000000000000000000000)) (.exp (-30211007459130633843120949593628389229581921670578606283311/16000000000000000000000000000000000000000000000000000000000) (151345804230351283832879/1000000000000000000000000) (1891822552879391047911/12500000000000000000000) { parts := 2, inner := (-30211007459130633843120949593628389229581921670578606283311/32000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (389031880737750442571189945621/1000000000000000000000000000000), innerHi := (194515940368875221285594972811/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell077
