import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell152.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell152
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(99561336276042051331976544359/1000000000000000000000000000000)]
def alpha : ℚ := (172847928923185811885707557903/1000000000000000000000000000000)
def D : ℚ := (371632361304816913687881429817/250000000000000000000000000000)
def mlo : ℚ := (16244937949052906596995427824951/1000000000000000000000000000000)
def mhi : ℚ := (5494611365120836054866100587851/250000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (2052888033503094824031100331001303986123268674585186808309915550879064597886992757417/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (398383688280742198628559/50000000000000000000000)) (.exp (-1617367729929093310697314588342708757893279395951028538501409/1000000000000000000000000000000000000000000000000000000000000) (198420308113023254906907/1000000000000000000000000) (49605077028255813726727/250000000000000000000000) { parts := 2, inner := (-1617367729929093310697314588342708757893279395951028538501409/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (445443944972903694881488914849/1000000000000000000000000000000), innerHi := (8908878899458073897629778297/20000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (298338057186957908308689278604798502929977748970941099102234239716246692029059901717/312500000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (398383688280742198628559/50000000000000000000000)) (.exp (-547050849828958031559385816645320641542118322009073477982509/250000000000000000000000000000000000000000000000000000000000) (1121179990536678422559/10000000000000000000000) (112117999053667842255901/1000000000000000000000000) { parts := 3, inner := (-547050849828958031559385816645320641542118322009073477982509/750000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (60274709483023159690120009517/125000000000000000000000000000), innerHi := (482197675864185277520960076137/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell152
