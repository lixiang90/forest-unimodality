import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell066.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell066
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(4687005562689058065593259963/50000000000000000000000000000)]
def alpha : ℚ := (34419833532366561344000000000028587/188257608000000000000000000000000000)
def D : ℚ := (815321004541666666666666666667/500000000000000000000000000000)
def mlo : ℚ := (17308636792947843425333193409591/1000000000000000000000000000000)
def mhi : ℚ := (15883219645293315143246930422919/800000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (11051498947151641492201941975967115850269030697207035714532374037499628941672150698288853829677/9412880400000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5912283331729730306847159/1000000000000000000000000)) (.exp (-81125676931111040297046777073922499627668490486260800505133/50000000000000000000000000000000000000000000000000000000000) (39480379537298234795493/200000000000000000000000) (98700948843245586988733/500000000000000000000000) { parts := 2, inner := (-81125676931111040297046777073922499627668490486260800505133/100000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (444299333430167520409513708087/1000000000000000000000000000000), innerHi := (55537416678770940051189213511/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (697561072851524956933910172692234516109941605146349589050477577045721417787220488608538822786499/753030432000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (5912283331729730306847159/1000000000000000000000000)) (.exp (-74444738830901895801995866020776878235914211434299500291997/40000000000000000000000000000000000000000000000000000000000) (155498612415982778957333/1000000000000000000000000) (77749306207991389478667/500000000000000000000000) { parts := 2, inner := (-74444738830901895801995866020776878235914211434299500291997/80000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (78866624732134385657693380367/200000000000000000000000000000), innerHi := (98583280915167982072116725459/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell066
