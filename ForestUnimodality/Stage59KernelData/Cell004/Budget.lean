import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell004.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell004
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(178771866626511003317442828407/1000000000000000000000000000000)]
def alpha : ℚ := (8458603/30625000)
def D : ℚ := (63356039/40000000)
def mlo : ℚ := (105/4)
def mhi : ℚ := (175/4)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (1238033285982923923495429685926804637/224000000000000000000000000000000000)) (.mul (.rat (988267943224736995944113/2000000000000000000000)) (.exp (-3754209199156731069666299396547/800000000000000000000000000000) (9161352128153204043141/1000000000000000000000000) (4580676064076602021571/500000000000000000000000) { parts := 5, inner := (-3754209199156731069666299396547/4000000000000000000000000000000), terms := 40, innerLo := (39119375690164947123669322081/100000000000000000000000000000), innerHi := (391193756901649471236693220811/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (53679458782123828876198397608934879/44800000000000000000000000000000000)) (.mul (.rat (988267943224736995944113/2000000000000000000000)) (.exp (-1251403066385577023222099798849/160000000000000000000000000000) (100278070495427087767/250000000000000000000000) (401112281981708351069/1000000000000000000000000) { parts := 8, inner := (-1251403066385577023222099798849/1280000000000000000000000000000), terms := 40, innerLo := (94047716164693590723738662751/250000000000000000000000000000), innerHi := (75238172931754872578990930201/200000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]

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
end ForestUnimodality.Stage59KernelData.Cell004
