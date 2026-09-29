import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell060.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell060
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(46560078071670789376505151289/500000000000000000000000000000)]
def alpha : ℚ := (166098124831919817190000000000065009/903640360000000000000000000000000000)
def D : ℚ := (817023234106240552796372273807/500000000000000000000000000000)
def mlo : ℚ := (8700441477333907612792074943469/500000000000000000000000000000)
def mhi : ℚ := (79839345321417034564444923010657/4000000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (15592419845996723642178261072691742993821288895899269471527638912338160830733836126511765560329/14119380625000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5539304053742922562264539/1000000000000000000000000)) (.exp (-405093234442669479101000616916370284851382635332021967481541/250000000000000000000000000000000000000000000000000000000000) (98912454472189316370659/500000000000000000000000) (197824908944378632741319/1000000000000000000000000) { parts := 2, inner := (-405093234442669479101000616916370284851382635332021967481541/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (444775121768718796155855426413/1000000000000000000000000000000), innerHi := (222387560884359398077927713207/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (450264268626224482947246959822055212144663392420007677946694132010478650894889179907504589928307/516365920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5539304053742922562264539/1000000000000000000000000)) (.exp (-3717326151356261102338593896409058661012120556808371144286873/2000000000000000000000000000000000000000000000000000000000000) (38970223019459568870117/250000000000000000000000) (155880892077838275480469/1000000000000000000000000) { parts := 2, inner := (-3717326151356261102338593896409058661012120556808371144286873/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (19740877138430189032084402009/50000000000000000000000000000), innerHi := (394817542768603780641688040181/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
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
    row.A row.B row.dδ row.dM alpha 0 D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell060
