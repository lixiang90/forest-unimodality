import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell196.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell196
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(99703725840916111205238966653/1000000000000000000000000000000)]
def alpha : ℚ := (47462374407634317891314945187/250000000000000000000000000000)
def D : ℚ := (1602534172814988290398126463701/1000000000000000000000000000000)
def mlo : ℚ := (16660693416439423451499805220101/1000000000000000000000000000000)
def mhi : ℚ := (1339502332814930015552099533437/50000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (53156255710138986582796382093160072053086170310710608850762812344637103870470739461671/62500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (25019644251168532411711/6250000000000000000000)) (.exp (-1661133208712232272701854353648395370926746633615304464291953/1000000000000000000000000000000000000000000000000000000000000) (18992363499125690244867/100000000000000000000000) (189923634991256902448671/1000000000000000000000000) { parts := 2, inner := (-1661133208712232272701854353648395370926746633615304464291953/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (108950572219486559257658303923/250000000000000000000000000000), innerHi := (435802288877946237030633215693/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (2294621252340831609670435139044316454806251197956729918763677726511717738543445054707/6250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (25019644251168532411711/6250000000000000000000)) (.exp (-133553373354247350825928961085891139450182631034213301476361/50000000000000000000000000000000000000000000000000000000000) (69178340280203175295049/1000000000000000000000000) (1383566805604063505901/20000000000000000000000) { parts := 3, inner := (-44517791118082450275309653695297046483394210344737767158787/50000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (205254829122981977071978216087/500000000000000000000000000000), innerHi := (16420386329838558165758257287/40000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell196
