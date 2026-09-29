import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell076.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell076
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(18927750485838141648292117761/200000000000000000000000000000)]
def alpha : ℚ := (57025217481449/306281250000000)
def D : ℚ := (325140863437269025994362668337/200000000000000000000000000000)
def mlo : ℚ := (4293367346938775510204081632653/250000000000000000000000000000)
def mhi : ℚ := (74249999999999999999999999999999/4000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (3311945529827766624055273693066708652612011771974367692063231047060430526648521273581274061/2722500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3083602406742841139930533/500000000000000000000000)) (.exp (-81263785886902021413458250489190167688745765011735818849933/50000000000000000000000000000000000000000000000000000000000) (196857390646464625931443/1000000000000000000000000) (49214347661616156482861/250000000000000000000000) { parts := 2, inner := (-81263785886902021413458250489190167688745765011735818849933/100000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (443686139795311417536669696309/1000000000000000000000000000000), innerHi := (44368613979531141753666969631/100000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (557720436802481978368673310389388743316257010023587816084003248774641547225368586122962767343/522720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3083602406742841139930533/500000000000000000000000)) (.exp (-1405385473573482017385689743754231072249514161858351707882239/800000000000000000000000000000000000000000000000000000000000) (172608053421842461946449/1000000000000000000000000) (3452161068436849238929/20000000000000000000000) { parts := 2, inner := (-1405385473573482017385689743754231072249514161858351707882239/1600000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (207730626907686906654574942601/500000000000000000000000000000), innerHi := (415461253815373813309149885203/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell076
