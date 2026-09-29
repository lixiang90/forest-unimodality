import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell084.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell084
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(19041642652806594507215475767/200000000000000000000000000000)]
def alpha : ℚ := (968160628790668533333333333333793/5227200000000000000000000000000000)
def D : ℚ := (50702736843511450381679389313/31250000000000000000000000000)
def mlo : ℚ := (1708629441624365482233502538071/100000000000000000000000000000)
def mhi : ℚ := (147746192893401015228426395939081/8000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (131746491168286472050760113551707669907895996104796609724653700737350334576402080639923/104544000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3197027600362643440234933/500000000000000000000000)) (.exp (-32535111253475633051414868747065748521043215808484295425457/20000000000000000000000000000000000000000000000000000000000) (2457078596007537338637/12500000000000000000000) (196566287680602987090961/1000000000000000000000000) { parts := 2, inner := (-32535111253475633051414868747065748521043215808484295425457/40000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (443357967877654125160543424329/1000000000000000000000000000000), innerHi := (44335796787765412516054342433/100000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (9243756606149533736330217205817505431605596783053397293480511528388953766399028469803053/8363520000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3197027600362643440234933/500000000000000000000000)) (.exp (-2813330208388775328563521003422751977496005699096086163750127/1600000000000000000000000000000000000000000000000000000000000) (43083045231688006635821/250000000000000000000000) (34466436185350405308657/200000000000000000000000) { parts := 2, inner := (-2813330208388775328563521003422751977496005699096086163750127/3200000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (415129113561976072763978131549/1000000000000000000000000000000), innerHi := (8302582271239521455279562631/20000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell084
