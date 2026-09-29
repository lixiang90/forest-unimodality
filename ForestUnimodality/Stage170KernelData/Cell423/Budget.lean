import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell423.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell423
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(118379618915763648402513570053/1000000000000000000000000000000)]
def R : ℚ := (5095673/2500000)
def D : ℚ := (1405101735662650602409638554217/500000000000000000000000000000)
def vmax : ℚ := (3569/15876)
def mlo : ℚ := (4282817610141328277508483223323/100000000000000000000000000000)
def mhi : ℚ := (475868623349036475278720358147/10000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (4047541255372823316015629470368120913784940535018345680045499085595134514743499822348029/15312500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (20597741891328462671140187/2500000000000000000000000)) (.exp (-506998316574252047609609020856953961010449848516797603946119/100000000000000000000000000000000000000000000000000000000000) (1256505180313912724483/200000000000000000000000) (392657868848097726401/62500000000000000000000) { parts := 6, inner := (-168999438858084015869869673618984653670149949505599201315373/200000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (429558563425624946312953313101/1000000000000000000000000000000), innerHi := (214779281712812473156476656551/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (18231044008088027281240224663138450866484584315081152010259986555393814143611871935891103/73500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (20597741891328462671140187/2500000000000000000000000)) (.exp (-56333146286028005289956557872994884556716649835199733771791/10000000000000000000000000000000000000000000000000000000000) (1788350112279367252539/500000000000000000000000) (3576700224558734505079/1000000000000000000000000) { parts := 6, inner := (-18777715428676001763318852624331628185572216611733244590597/20000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (391063326624779607836510582753/1000000000000000000000000000000), innerHi := (195531663312389803918255291377/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell423
