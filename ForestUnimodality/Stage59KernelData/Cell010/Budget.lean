import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell010.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell010
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(12549398151803045997099287937/62500000000000000000000000000)]
def alpha : ℚ := (3803687/11250000)
def D : ℚ := (3383039/2000000)
def mlo : ℚ := (45/2)
def mhi : ℚ := (75/2)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (120368239602406905116580143744901/80000000000000000000000000000000)) (.mul (.rat (4623800176771393921626441/100000000000000000000000)) (.exp (-112944583366227413973893591433/25000000000000000000000000000) (682074235124101257323/62500000000000000000000) (10913187761985620117169/1000000000000000000000000) { parts := 5, inner := (-112944583366227413973893591433/125000000000000000000000000000), terms := 40, innerLo := (1266019360499321502408005033/3125000000000000000000000000), innerHi := (405126195359782880770561610561/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (49191632062758685529271129744901/48000000000000000000000000000000)) (.mul (.rat (4623800176771393921626441/100000000000000000000000)) (.exp (-37648194455409137991297863811/5000000000000000000000000000) (67116514082015217153/125000000000000000000000) (21477284506244869489/40000000000000000000000) { parts := 8, inner := (-37648194455409137991297863811/40000000000000000000000000000), terms := 40, innerLo := (195078733192655544490764995097/500000000000000000000000000000), innerHi := (78031493277062217796305998039/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell010
