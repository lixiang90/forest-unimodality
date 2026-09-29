import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell194.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell194
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(49465896368767294135323398961/500000000000000000000000000000)]
def alpha : ℚ := (93988788832852991545647269553/500000000000000000000000000000)
def D : ℚ := (160489520013793103448275862069/100000000000000000000000000000)
def mlo : ℚ := (8362925303089558075870160344153/500000000000000000000000000000)
def mhi : ℚ := (1339502332814930015552099533437/50000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (25970189166762971210055788918811119143390139901353885829832433350130221537427065115949/31250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3987121734462146349642353/1000000000000000000000000)) (.exp (-413679596382369893543119109652712344961567747468857482625033/250000000000000000000000000000000000000000000000000000000000) (23893234696463159479209/125000000000000000000000) (191145877571705275833673/1000000000000000000000000) { parts := 2, inner := (-413679596382369893543119109652712344961567747468857482625033/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (218601165122527009276014960549/500000000000000000000000000000), innerHi := (437202330245054018552029921099/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (876275165149821098824098882690338268647371834766369370575819156747253157635780290799/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3987121734462146349642353/1000000000000000000000000)) (.exp (-66259683580745366156693691329873802188075709322477110558957/25000000000000000000000000000000000000000000000000000000000) (70623852090757710423937/1000000000000000000000000) (35311926045378855211969/500000000000000000000000) { parts := 3, inner := (-22086561193581788718897897109957934062691903107492370186319/25000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (20667461548982456771243116201/50000000000000000000000000000), innerHi := (413349230979649135424862324021/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell194
