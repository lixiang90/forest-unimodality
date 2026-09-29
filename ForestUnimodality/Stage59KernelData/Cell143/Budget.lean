import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell143.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell143
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(70973423750888303823426300767/500000000000000000000000000000)]
def alpha : ℚ := (85880049892071407937509287683/500000000000000000000000000000)
def D : ℚ := (1480559545488693189361419657477/1000000000000000000000000000000)
def mlo : ℚ := (44198390946865882768985942887453/2000000000000000000000000000000)
def mhi : ℚ := (27864202988241534789143311820351/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (1948599582876641926180571489586636682393000277409742255219115963769013711281570053055741/4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1065505410028338539873971/125000000000000000000000)) (.exp (-3136911129779337631848454043837275148179484949897958408576451/1000000000000000000000000000000000000000000000000000000000000) (43416699543404322349343/1000000000000000000000000) (1356771860731385073417/31250000000000000000000) { parts := 4, inner := (-3136911129779337631848454043837275148179484949897958408576451/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (456472061458267544138924622861/1000000000000000000000000000000), innerHi := (228236030729133772069462311431/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (70083722588757721728074272539870064958808689137409161538335351167804758168628090491097/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1065505410028338539873971/125000000000000000000000)) (.exp (-1977617886165234593991416679810469957783017859603808797509217/500000000000000000000000000000000000000000000000000000000000) (1915415199817070463077/100000000000000000000000) (19154151998170704630771/1000000000000000000000000) { parts := 4, inner := (-1977617886165234593991416679810469957783017859603808797509217/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (93004880919330879536520972999/250000000000000000000000000000), innerHi := (372019523677323518146083891997/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell143
