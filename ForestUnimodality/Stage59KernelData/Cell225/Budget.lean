import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell225.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell225
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(61630878006733697729171801531/1000000000000000000000000000000)]
def alpha : ℚ := (376455431544469639707734945831/1000000000000000000000000000000)
def D : ℚ := (2334529135219512195121951219513/1000000000000000000000000000000)
def mlo : ℚ := (288433734939759036144578313253/20000000000000000000000000000)
def mhi : ℚ := (12144578313253012048192771084337/500000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (10129700658615410540090826201806733405715056774491329427774148841447858271984343423213/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1484594264375438221748027/200000000000000000000000)) (.exp (-17776424331098852092004493116290100832795099594003262990343/20000000000000000000000000000000000000000000000000000000000) (411140112376774867394627/1000000000000000000000000) (102785028094193716848657/250000000000000000000000) { parts := 1, inner := (-17776424331098852092004493116290100832795099594003262990343/20000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (411140112376774867394627729573/1000000000000000000000000000000), innerHi := (205570056188387433697313864787/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (166332947181409862184906719967783600347224388166980601694166722257603641161335506619373/62500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1484594264375438221748027/200000000000000000000000)) (.exp (-748481024467320088084399710159592924151057888226094626719947/500000000000000000000000000000000000000000000000000000000000) (223809049350122843802647/1000000000000000000000000) (27976131168765355475331/125000000000000000000000) { parts := 2, inner := (-748481024467320088084399710159592924151057888226094626719947/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (11827115279890814414072530159/25000000000000000000000000000), innerHi := (473084611195632576562901206361/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell225
