import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell317.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell317
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(28454796869942295217164016983/250000000000000000000000000000)]
def R : ℚ := (43935559/25000000)
def D : ℚ := (2300991799491525423728813559323/1000000000000000000000000000000)
def vmax : ℚ := (31860/137641)
def mlo : ℚ := (24247480284033888854715839404311/500000000000000000000000000000)
def mhi : ℚ := (557692046532779443658464306299153/10000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (16450406970706297154353020671659302388334828646029529819053995752621858745125123162814775813/49157500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2821478170138152830048739/250000000000000000000000)) (.exp (-689957126090115015972986196461743032786789201781894607413713/125000000000000000000000000000000000000000000000000000000000) (4007222148656837316809/1000000000000000000000000) (400722214865683731681/100000000000000000000000) { parts := 6, inner := (-229985708696705005324328732153914344262263067260631535804571/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (39854182316161899261800115217/100000000000000000000000000000), innerHi := (398541823161618992618001152171/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (15198647416486841342549313190333913757924972413392154747987644169023687958994025246470259750553/49157500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2821478170138152830048739/250000000000000000000000)) (.exp (-15869013900072645367378682518620089754096151640983575970515399/2500000000000000000000000000000000000000000000000000000000000) (1750934628772340310481/1000000000000000000000000) (875467314386170155241/500000000000000000000000) { parts := 7, inner := (-15869013900072645367378682518620089754096151640983575970515399/17500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (201907021964559701977085237441/500000000000000000000000000000), innerHi := (403814043929119403954170474883/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell317
