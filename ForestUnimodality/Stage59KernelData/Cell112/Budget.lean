import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell112.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell112
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(139326929734016641652723819589/1000000000000000000000000000000)]
def alpha : ℚ := (174436053403571922353768831267/1000000000000000000000000000000)
def D : ℚ := (1465754823295198010330973789937/1000000000000000000000000000000)
def mlo : ℚ := (16712854279988548525622673919267/1000000000000000000000000000000)
def mhi : ℚ := (22119954194102490695677068422559/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (13854167618786827939161200493663002675741099853186857325214208780050146898467119010663/31250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (35102733314919185025893/7812500000000000000000)) (.exp (-2328550673922823792271030959051414425526174677314408859121263/1000000000000000000000000000000000000000000000000000000000000) (97436862589473315683193/1000000000000000000000000) (48718431294736657841597/500000000000000000000000) { parts := 3, inner := (-776183557974274597423676986350471475175391559104802953040421/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (460158833917032142522799913619/1000000000000000000000000000000), innerHi := (23007941695851607126139995681/50000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (26455461441965037440795790210039525323906738112481661811353939325985812676266881360471/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (35102733314919185025893/7812500000000000000000)) (.exp (-3081905303721384430946952739920952800185595715569809533708251/1000000000000000000000000000000000000000000000000000000000000) (286698585460018644913/6250000000000000000000) (45871773673602983186081/1000000000000000000000000) { parts := 4, inner := (-3081905303721384430946952739920952800185595715569809533708251/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (462792575698045773632078034001/1000000000000000000000000000000), innerHi := (231396287849022886816039017001/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell112
