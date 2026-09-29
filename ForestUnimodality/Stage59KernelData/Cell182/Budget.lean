import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell182.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell182
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(25269478167954000930997157823/250000000000000000000000000000)]
def alpha : ℚ := (174784241504723289548035133699/1000000000000000000000000000000)
def D : ℚ := (752773710912623793406042371819/500000000000000000000000000000)
def mlo : ℚ := (8488945054256441320535984710023/500000000000000000000000000000)
def mhi : ℚ := (27353267397048533143949284065629/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (310213083735165146439340406300414158529551108098977170535422794817529877617252559151/156250000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (131859865750076710178007/12500000000000000000000)) (.exp (-214511211717494235853345077815922751990581630027997820959929/125000000000000000000000000000000000000000000000000000000000) (89883861090906588183289/500000000000000000000000) (179767722181813176366579/1000000000000000000000000) { parts := 2, inner := (-214511211717494235853345077815922751990581630027997820959929/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (42399023830957851000185048721/100000000000000000000000000000), innerHi := (423990238309578510001850487211/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (235462179009878309632166917925614544408224643815673942253626184303002443425162769173/312500000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (131859865750076710178007/12500000000000000000000)) (.exp (-691202793311925871083000806295734243428651060756261202765667/250000000000000000000000000000000000000000000000000000000000) (15746998010780357765719/250000000000000000000000) (62987992043121431062877/1000000000000000000000000) { parts := 3, inner := (-230400931103975290361000268765244747809550353585420400921889/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (1989402192881064540498458743/5000000000000000000000000000), innerHi := (397880438576212908099691748601/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell182
