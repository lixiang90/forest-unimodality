import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell136.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell136
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(12303204206562412702126801723/125000000000000000000000000000)]
def alpha : ℚ := (85822470328088888352051189529/500000000000000000000000000000)
def D : ℚ := (368382978206222541020353268179/250000000000000000000000000000)
def mlo : ℚ := (16388697326586359768931082351887/1000000000000000000000000000000)
def mhi : ℚ := (11086471720926066902512202767453/500000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (6573389756761820162918017752829505414175003776486521170517851373420066497497058089518179/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6422779302466613771116499/1000000000000000000000000)) (.exp (-201633489888535468679125806608593780241029625579148163901301/125000000000000000000000000000000000000000000000000000000000) (49818828691760243836319/250000000000000000000000) (199275314767040975345277/1000000000000000000000000) { parts := 2, inner := (-201633489888535468679125806608593780241029625579148163901301/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (55800329687511840361168926213/125000000000000000000000000000), innerHi := (89280527500018944577870281941/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (948858891527229929875620741862681589919773836560324875540371736223900876426248025918737/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6422779302466613771116499/1000000000000000000000000)) (.exp (-136399125512832817047643927999931448492584939727444408721519/62500000000000000000000000000000000000000000000000000000000) (56386067069868401589939/500000000000000000000000) (112772134139736803179879/1000000000000000000000000) { parts := 3, inner := (-136399125512832817047643927999931448492584939727444408721519/187500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (483133627194420759991005608571/1000000000000000000000000000000), innerHi := (120783406798605189997751402143/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell136
