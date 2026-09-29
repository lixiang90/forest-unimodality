import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell414.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell414
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(26642894181863998810416339533/250000000000000000000000000000)]
def R : ℚ := (1199131211/800000000)
def D : ℚ := (2379308466666666666666666666667/1000000000000000000000000000000)
def vmax : ℚ := (6/25)
def mlo : ℚ := (22486460641327793891804331646121/500000000000000000000000000000)
def mhi : ℚ := (49969912536283986426231848102491/1000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (17141248566457309834238407208773127235270288981157838325797879756041880452013787092441001/50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (16293780957834023581654037/1000000000000000000000000)) (.exp (-599104391391546083238102024469708847625828953080933138401493/125000000000000000000000000000000000000000000000000000000000) (8288923851299283715177/1000000000000000000000000) (4144461925649641857589/500000000000000000000000) { parts := 5, inner := (-599104391391546083238102024469708847625828953080933138401493/625000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (383441954745402538391602255709/1000000000000000000000000000000), innerHi := (38344195474540253839160225571/100000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (16031573663760361223831583022478283524646435362218492799393195874837220998773911388209701/50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (16293780957834023581654037/1000000000000000000000000)) (.exp (-1331343091981213518306893387710461145513599688624428039076703/250000000000000000000000000000000000000000000000000000000000) (4866538533940839283083/1000000000000000000000000) (1216634633485209820771/250000000000000000000000) { parts := 6, inner := (-1331343091981213518306893387710461145513599688624428039076703/1500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (411658127663624700827760762671/1000000000000000000000000000000), innerHi := (25728632978976543801735047667/62500000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell414
