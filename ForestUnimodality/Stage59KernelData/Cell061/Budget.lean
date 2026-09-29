import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell061.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell061
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(46560078071670789376505151289/500000000000000000000000000000)]
def alpha : ℚ := (166098124831919817190000000000065009/903640360000000000000000000000000000)
def D : ℚ := (817023234106240552796372273807/500000000000000000000000000000)
def mlo : ℚ := (79839345321417034564444923010657/4000000000000000000000000000000)
def mhi : ℚ := (45037579412081404113276623236781/2000000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (6294376227278526032972906167311589319544726678721307551895218741503791328666791015013344517/5163659200000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7725459218877839262518137/1000000000000000000000000)) (.exp (-3717326151356261102338593896409058661012120556808371144286873/2000000000000000000000000000000000000000000000000000000000000) (38970223019459568870117/250000000000000000000000) (155880892077838275480469/1000000000000000000000000) { parts := 2, inner := (-3717326151356261102338593896409058661012120556808371144286873/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (19740877138430189032084402009/50000000000000000000000000000), innerHi := (394817542768603780641688040181/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (17415740325407776276218736070375448774916168431652918355284985751305885455251746725570565127/18072807200000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7725459218877839262518137/1000000000000000000000000)) (.exp (-2096953213585583185934591428743577521606590015480283274360709/1000000000000000000000000000000000000000000000000000000000000) (15353761973558295369671/125000000000000000000000) (122830095788466362957369/1000000000000000000000000) { parts := 3, inner := (-2096953213585583185934591428743577521606590015480283274360709/3000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (49708988976138218886460962299/100000000000000000000000000000), innerHi := (497089889761382188864609622991/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell061
