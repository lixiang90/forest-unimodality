import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell015.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell015
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(49669039857309676523113134711/500000000000000000000000000000)]
def alpha : ℚ := (4032625379/13005000000)
def D : ℚ := (2322293575442247658688865764829/1000000000000000000000000000000)
def mlo : ℚ := (2516447368421052631578947368421/125000000000000000000000000000)
def mhi : ℚ := (33552631578947368421052631578947/1000000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (3988840143814877260138039512948554767747090612659756043243553877094422553354696804578763319/1625625000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (536993919473990377611017/50000000000000000000000)) (.exp (-124989524640927310987439302808928306892639088964393520361331/62500000000000000000000000000000000000000000000000000000000) (13535796810861074619139/100000000000000000000000) (135357968108610746191391/1000000000000000000000000) { parts := 2, inner := (-124989524640927310987439302808928306892639088964393520361331/125000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (183955135908603232854271377313/500000000000000000000000000000), innerHi := (367910271817206465708542754627/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (884736913076147495162968220741064801449608613301892978684126605156879341995082245111208677/406406250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (536993919473990377611017/50000000000000000000000)) (.exp (-1666526995212364146499190704119060648248473622750754642529317/500000000000000000000000000000000000000000000000000000000000) (35683960016309927455883/1000000000000000000000000) (8920990004077481863971/250000000000000000000000) { parts := 4, inner := (-1666526995212364146499190704119060648248473622750754642529317/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (217314280024393303576612447499/500000000000000000000000000000), innerHi := (434628560048786607153224894999/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell015
