import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell092.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell092
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(748105779492800408682327849/7812500000000000000000000000)]
def alpha : ℚ := (187418723169/1000000000000)
def D : ℚ := (1619335743149367088607594936709/1000000000000000000000000000000)
def mlo : ℚ := (17/1)
def mhi : ℚ := (147/8)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (1255637156304211676681634048904659292950208221284408639/1000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6394814833788522001611909/1000000000000000000000000)) (.exp (-12717798251377606947599573433/7812500000000000000000000000) (24543217940998745501931/125000000000000000000000) (196345743527989964015449/1000000000000000000000000) { parts := 2, inner := (-12717798251377606947599573433/15625000000000000000000000000), terms := 40, innerLo := (221554588943667540103826816439/500000000000000000000000000000), innerHi := (443109177887335080207653632879/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (1100738460380683799350642189872323808937708221284408639/1000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6394814833788522001611909/1000000000000000000000000)) (.exp (-109971549585441660076302193803/62500000000000000000000000000) (5378849925434464119329/31250000000000000000000) (172123197613902851818529/1000000000000000000000000) { parts := 2, inner := (-109971549585441660076302193803/125000000000000000000000000000), terms := 40, innerLo := (20743866419613223337228047127/50000000000000000000000000000), innerHi := (414877328392264466744560942541/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell092
