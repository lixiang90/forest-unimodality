import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell057.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell057
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(18560095437838843651818191869/200000000000000000000000000000)]
def alpha : ℚ := (18865385655133798050285714285721563/103273184000000000000000000000000000)
def D : ℚ := (408940629765724802425029771571/250000000000000000000000000000)
def mlo : ℚ := (3489570287194990282876268624487/200000000000000000000000000000)
def mhi : ℚ := (40027423882530770891816022457351/2000000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (7373792006350893096175279558938748020486934709393444959335816342623692676608449809556836029223/6454574000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5701462279710511005248463/1000000000000000000000000)) (.exp (-64766757567385722561458074766011822987023796003652077696203/40000000000000000000000000000000000000000000000000000000000) (198063233297332293687703/1000000000000000000000000) (24757904162166536710963/125000000000000000000000) { parts := 2, inner := (-64766757567385722561458074766011822987023796003652077696203/80000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (44504295668770255653115943057/100000000000000000000000000000), innerHi := (445042956687702556531159430571/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (116587764622913459690111277085740016715312084839555380577136887628352423566911537477003373766679/129091480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5701462279710511005248463/1000000000000000000000000)) (.exp (-742912807390600935263783798786608388391795052847026987479019/400000000000000000000000000000000000000000000000000000000000) (7804816061609506234603/50000000000000000000000) (156096321232190124692061/1000000000000000000000000) { parts := 2, inner := (-742912807390600935263783798786608388391795052847026987479019/800000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (6173285464469277818004324749/15625000000000000000000000000), innerHi := (395090269726033780352276783937/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell057
