import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell124.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell124
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(139742682533639181274359559727/1000000000000000000000000000000)]
def alpha : ℚ := (170057567664516740820338608547/1000000000000000000000000000000)
def D : ℚ := (734053136358490566037735849057/500000000000000000000000000000)
def mlo : ℚ := (16500068284244548641143533482041/1000000000000000000000000000000)
def mhi : ℚ := (43676651340647334638321118040697/2000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (7242092726791535494367732440369318127701330353953327541024248769999792569452803602223/50000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (56843800686987033810027/50000000000000000000000)) (.exp (-2305763804028554501168140526242476940748413412366852021362807/1000000000000000000000000000000000000000000000000000000000000) (24920658392965137888809/250000000000000000000000) (99682633571860551555237/1000000000000000000000000) { parts := 3, inner := (-2305763804028554501168140526242476940748413412366852021362807/3000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (46366733483428510806869765169/100000000000000000000000000000), innerHi := (463667334834285108068697651691/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (682098788057586408514613433955545095191768708471941770748229710266413600888516569441/8000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (56843800686987033810027/50000000000000000000000)) (.exp (-6103492422428526620739195510641883606141690477249025788209719/2000000000000000000000000000000000000000000000000000000000000) (9455259573789850670557/200000000000000000000000) (23638148934474626676393/500000000000000000000000) { parts := 4, inner := (-6103492422428526620739195510641883606141690477249025788209719/8000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (466295114304066563429791260961/1000000000000000000000000000000), innerHi := (233147557152033281714895630481/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell124
