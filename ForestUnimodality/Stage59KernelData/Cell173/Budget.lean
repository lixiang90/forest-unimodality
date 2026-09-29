import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell173.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell173
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(25180925628998892555349671597/250000000000000000000000000000)]
def alpha : ℚ := (173714731451706108706125690387/1000000000000000000000000000000)
def D : ℚ := (188342314326328024377218609619/125000000000000000000000000000)
def mlo : ℚ := (4254470080817386206607763493991/250000000000000000000000000000)
def mhi : ℚ := (685442401909467777731250785143/25000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (4756524173842030705011170386833889698581809288697829510290378555233477685323327705463/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (203323607391007854516829/20000000000000000000000)) (.exp (-107131494695863510008629537453489117160926705750547132873627/62500000000000000000000000000000000000000000000000000000000) (180125055753853959800319/1000000000000000000000000) (70361349903849203047/390625000000000000000) { parts := 2, inner := (-107131494695863510008629537453489117160926705750547132873627/125000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (424411422741959149310802619083/1000000000000000000000000000000), innerHi := (106102855685489787327700654771/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (178456275505922448248308414639133779254999263747614581877057519309977524919802552199/250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (203323607391007854516829/20000000000000000000000)) (.exp (-17260074145444676612501425478617830992180574809213456683371/6250000000000000000000000000000000000000000000000000000000) (3085441057518129357/48828125000000000000) (63189832857971289231361/1000000000000000000000000) { parts := 3, inner := (-5753358048481558870833808492872610330726858269737818894457/6250000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (79660995838870877521422470419/200000000000000000000000000000), innerHi := (12447030599823574612722261003/31250000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell173
