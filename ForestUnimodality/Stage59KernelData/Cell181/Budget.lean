import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell181.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell181
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(101051540006951311845677268873/1000000000000000000000000000000)]
def alpha : ℚ := (87332626898910530358076941031/500000000000000000000000000000)
def D : ℚ := (1505679488884941326450642117473/1000000000000000000000000000000)
def mlo : ℚ := (3396464836404663407295975930801/200000000000000000000000000000)
def mhi : ℚ := (6840102795537169361915507082863/250000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (1987175271813496973744984247270117947244193287248530659534414954759522176738917137681/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (528401920837461069879737/50000000000000000000000)) (.exp (-343218002298149186739631647478684976206415577233933719257273/200000000000000000000000000000000000000000000000000000000000) (179767665060486143807443/1000000000000000000000000) (44941916265121535951861/250000000000000000000000) { parts := 2, inner := (-343218002298149186739631647478684976206415577233933719257273/400000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (211995085473983419774096873551/500000000000000000000000000000), innerHi := (423990170947966839548193747103/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (941303575372955093378397661967508645347948990564671247893459223050488190993517228303/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (528401920837461069879737/50000000000000000000000)) (.exp (-691202921294883778850647067839005723417641613015469141623399/250000000000000000000000000000000000000000000000000000000000) (62987959797571547426833/1000000000000000000000000) (31493979898785773713417/500000000000000000000000) { parts := 3, inner := (-230400973764961259616882355946335241139213871005156380541133/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (24867523167520716934097780021/62500000000000000000000000000), innerHi := (397880370680331470945564480337/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell181
