import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell011.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell011
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(12031573700581518794799261047/100000000000000000000000000000)]
def R : ℚ := (653615921568627450980392156863/500000000000000000000000000000)
def D : ℚ := (76410016897506925207756232687/50000000000000000000000000000)
def vmax : ℚ := (969/4900)
def mlo : ℚ := (560322368421052631578947368421048149/4000000000000000000000000000000000)
def mhi : ℚ := (1225/8)

def budgetExpression_lo : Expr := (.sub (.rat (25770644719134719035670750970072398972993507756190521938704596966882037395631213876266053843505939/56000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (37503212038764445424021687/100000000000000000000000)) (.exp (-6741559871742285356804330684946939488573657640664513986407152003/400000000000000000000000000000000000000000000000000000000000000) (47912007791859073/1000000000000000000000000) (23956003895929537/500000000000000000000000) { parts := 17, inner := (-6741559871742285356804330684946939488573657640664513986407152003/6800000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (371054671947598883069218473413/1000000000000000000000000000000), innerHi := (185527335973799441534609236707/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (14189324613265747065224231789624463426837050309886835417817/32000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (37503212038764445424021687/100000000000000000000000)) (.exp (-589547111328494420945163791303/32000000000000000000000000000) (9973370668504677/1000000000000000000000000) (4986685334252339/500000000000000000000000) { parts := 19, inner := (-589547111328494420945163791303/608000000000000000000000000000), terms := 40, innerLo := (379215795693597777814515684163/1000000000000000000000000000000), innerHi := (94803948923399444453628921041/250000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_hi_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms (∅ : Finset ℤ)
    row.A row.B row.dδ row.dM (R * vmax : ℚ) 0 D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ)) (fun _ => 0) (fun _ => 0)
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage170KernelData.Cell011
