import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell553.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell553
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(118379618915763648402513570053/1000000000000000000000000000000)]
def R : ℚ := (5095673/2500000)
def D : ℚ := (1405101735662650602409638554217/500000000000000000000000000000)
def vmax : ℚ := (3569/15876)
def mlo : ℚ := (8089766596933620079738246088499/200000000000000000000000000000)
def mhi : ℚ := (4282817610141328277508483223323/100000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (798471528261082117707458103728165280888686215781394940270908858765857039507190033860426353/2940000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (41310813032437430081245111/5000000000000000000000000)) (.exp (-957663486862476089929261483840913037464183047198395474120447/200000000000000000000000000000000000000000000000000000000000) (4163227705246312792059/500000000000000000000000) (8326455410492625584119/1000000000000000000000000) { parts := 5, inner := (-957663486862476089929261483840913037464183047198395474120447/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (191894283105146915287534703117/500000000000000000000000000000), innerHi := (76757713242058766115013881247/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (4025994223805336418424528303942376042515878959500308266883177727850370893790593049096301/15312500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (41310813032437430081245111/5000000000000000000000000)) (.exp (-506998316574252047609609020856953961010449848516797603946119/100000000000000000000000000000000000000000000000000000000000) (1256505180313912724483/200000000000000000000000) (392657868848097726401/62500000000000000000000) { parts := 6, inner := (-168999438858084015869869673618984653670149949505599201315373/200000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (429558563425624946312953313101/1000000000000000000000000000000), innerHi := (214779281712812473156476656551/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell553
