import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell202.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell202
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(100039438394037036923116479259/1000000000000000000000000000000)]
def alpha : ℚ := (113308987825975932841775990297/500000000000000000000000000000)
def D : ℚ := (1768064366666666666666666666667/1000000000000000000000000000000)
def mlo : ℚ := (1642268041237113402061855670103/100000000000000000000000000000)
def mhi : ℚ := (1653672680412371134020618556701/62500000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (25025397659741840782224857337111290581212495548729280587693807432387131339741728321649/50000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (623978034934173142467273/250000000000000000000000)) (.exp (-164291572537836082287138712844925769536643852233687545893677/100000000000000000000000000000000000000000000000000000000000) (19341527351412944469939/100000000000000000000000) (193415273514129444699391/1000000000000000000000000) { parts := 2, inner := (-164291572537836082287138712844925769536643852233687545893677/200000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (109947508360276588369391217811/250000000000000000000000000000), innerHi := (87958006688221270695512974249/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (6082613919039115880796853221169083421574418118662303575730898737816122665092473267737/31250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (623978034934173142467273/250000000000000000000000)) (.exp (-165432486236015499525243842795244006512214617411229181964559/62500000000000000000000000000000000000000000000000000000000) (8858646232609565645067/125000000000000000000000) (70869169860876525160537/1000000000000000000000000) { parts := 3, inner := (-55144162078671833175081280931748002170738205803743060654853/62500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (82765455753113344280813529853/200000000000000000000000000000), innerHi := (206913639382783360702033824633/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell202
