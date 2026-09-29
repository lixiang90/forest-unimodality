import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell230.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell230
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(31991254456640213713180887577/500000000000000000000000000000)]
def alpha : ℚ := (20944526272189349112426035503/50000000000000000000000000000)
def D : ℚ := (342313033551401869158878504673/125000000000000000000000000000)
def mlo : ℚ := (3611111111111111111111111111111/250000000000000000000000000000)
def mhi : ℚ := (23833333333333333333333333333333/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (503550147273867674359049818398743279127796303685750428568404877551891466303060093217/125000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (305242455240784309467017/40000000000000000000000)) (.exp (-115523974426756327297597649583607556527282595531809646568047/125000000000000000000000000000000000000000000000000000000000) (99213006781839944276101/250000000000000000000000) (79370405425471955420881/200000000000000000000000) { parts := 1, inner := (-115523974426756327297597649583607556527282595531809646568047/125000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (99213006781839944276101064529/250000000000000000000000000000), innerHi := (396852027127359777104404258117/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (1491655238469357422221953715605036019935858365508350481705214632655674398909180279651/500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (305242455240784309467017/40000000000000000000000)) (.exp (-762458231216591760164144487251822669581847786595428939704141/500000000000000000000000000000000000000000000000000000000000) (217639237158169573932281/1000000000000000000000000) (108819618579084786966141/500000000000000000000000) { parts := 2, inner := (-762458231216591760164144487251822669581847786595428939704141/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (93303641334766688500519035397/200000000000000000000000000000), innerHi := (233259103336916721251297588493/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell230
