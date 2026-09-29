import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell007.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell007
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(111619122497443426932542088359/1000000000000000000000000000000)]
def alpha : ℚ := (38629773371428571428571428571449/126000000000000000000000000000000)
def D : ℚ := (824881009467455621301775147929/500000000000000000000000000000)
def mlo : ℚ := (24230769230769230769230769230769/1000000000000000000000000000000)
def mhi : ℚ := (8076923076923076923076923076923/200000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (511377346087951328459387703842097976692197245775569276380553909942821202374020095941262759/350000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (689248439938581203279/100000000000000000000)) (.exp (-2704617198976513806442365987160358857125577513055323259518071/1000000000000000000000000000000000000000000000000000000000000) (33447963387552055199201/500000000000000000000000) (66895926775104110398403/1000000000000000000000000) { parts := 3, inner := (-901539066325504602147455329053452952375192504351774419839357/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (20297220167363604351572893203/50000000000000000000000000000), innerHi := (405944403347272087031457864061/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (376907399851846772496229764125892652581867555958953182550647519409691212697689005338526441/210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (689248439938581203279/100000000000000000000)) (.exp (-901539066325504602147455329053452952375192504351774419839357/200000000000000000000000000000000000000000000000000000000000) (11023837210712374493661/1000000000000000000000000) (5511918605356187246831/500000000000000000000000) { parts := 5, inner := (-901539066325504602147455329053452952375192504351774419839357/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (20297220167363604351572893203/50000000000000000000000000000), innerHi := (405944403347272087031457864061/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
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
    row.A row.B row.dδ row.dM alpha 0 D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell007
