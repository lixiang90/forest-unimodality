import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell033.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell033
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(28540061780381397000539871871/250000000000000000000000000000), (27264732272995161762543854481/200000000000000000000000000000)]
def R : ℚ := (365708962790697674418604651163/250000000000000000000000000000)
def D : ℚ := (6663680383/4000000000)
def vmax : ℚ := (860/3969)
def mlo : ℚ := (315/4)
def mhi : ℚ := (1449/16)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (2345814695766269994726763676265191346667968475269411461/5625000000000000000000000000000000000000000000000000000)) (.mul (.rat (4548441542058273001636337/2500000000000000000000000)) (.exp (-1798023892164028011034011927873/200000000000000000000000000000) (24927040664920949037/200000000000000000000000) (62317601662302372593/500000000000000000000000) { parts := 9, inner := (-199780432462669779003779103097/200000000000000000000000000000), terms := 40, innerLo := (184141767430079303318000766393/500000000000000000000000000000), innerHi := (368283534860158606636001532787/1000000000000000000000000000000) }))) (.mul (.rat (74864926685604986644761993/10000000000000000000000000)) (.exp (-1717678133198695191040262832303/160000000000000000000000000000) (10879442996171846799/500000000000000000000000) (21758885992343693599/1000000000000000000000000) { parts := 11, inner := (-1717678133198695191040262832303/1760000000000000000000000000000), terms := 40, innerLo := (188416438901245522828247749901/500000000000000000000000000000), innerHi := (376832877802491045656495499803/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (44579209403265335442154937667299449801488274931196463603/112500000000000000000000000000000000000000000000000000000)) (.mul (.rat (4548441542058273001636337/2500000000000000000000000)) (.exp (-41354549519772644253782274341079/4000000000000000000000000000000) (8089596204448994351/250000000000000000000000) (6471676963559195481/200000000000000000000000) { parts := 11, inner := (-41354549519772644253782274341079/44000000000000000000000000000000), terms := 40, innerLo := (97669056800820901362155483893/250000000000000000000000000000), innerHi := (390676227203283605448621935573/1000000000000000000000000000000) }))) (.mul (.rat (74864926685604986644761993/10000000000000000000000000)) (.exp (-39506597063569989393926045142969/3200000000000000000000000000000) (173917044487711339/40000000000000000000000) (1086981528048195869/250000000000000000000000) { parts := 13, inner := (-39506597063569989393926045142969/41600000000000000000000000000000), terms := 40, innerLo := (48358205757719602409613569777/125000000000000000000000000000), innerHi := (386865646061756819276908558217/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

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
end ForestUnimodality.Stage170KernelData.Cell033
