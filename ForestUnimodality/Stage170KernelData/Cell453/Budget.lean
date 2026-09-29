import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell453.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell453
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(71904276104401068679075255131/500000000000000000000000000000), (89012327689811778924543952919/500000000000000000000000000000)]
def R : ℚ := (53922541/50000000)
def D : ℚ := (883742337164179104477611940299/500000000000000000000000000000)
def vmax : ℚ := (20/81)
def mlo : ℚ := (765/16)
def mhi : ℚ := (405/8)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (234656710691151529981194821874557553389848911944020442482009/720000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7300845852116687240140891/500000000000000000000000)) (.exp (-11001354243973363507898514035043/1600000000000000000000000000000) (1032423422981589557047/1000000000000000000000000) (129052927872698694631/125000000000000000000000) { parts := 7, inner := (-11001354243973363507898514035043/11200000000000000000000000000000), terms := 40, innerLo := (374462441121981371028577054111/1000000000000000000000000000000), innerHi := (11701951285061917844643032941/31250000000000000000000000000) }))) (.mul (.rat (17285209058819841487775193/1000000000000000000000000)) (.exp (-13618886136541202175455224796607/1600000000000000000000000000000) (201080780956351968991/1000000000000000000000000) (6283774404885999031/31250000000000000000000) { parts := 9, inner := (-1513209570726800241717247199623/1600000000000000000000000000000), terms := 40, innerLo := (194192923648080121679016954759/500000000000000000000000000000), innerHi := (388385847296160243358033909519/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (12781123695485716645123079950883900199402877173177673087177/40000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (7300845852116687240140891/500000000000000000000000)) (.exp (-5824246364456486563005095665611/800000000000000000000000000000) (688973357835936229209/1000000000000000000000000) (68897335783593622921/100000000000000000000000) { parts := 8, inner := (-5824246364456486563005095665611/6400000000000000000000000000000), terms := 40, innerLo := (402508729384729865507107799711/1000000000000000000000000000000), innerHi := (12578397793272808297097118741/31250000000000000000000000000) }))) (.mul (.rat (17285209058819841487775193/1000000000000000000000000)) (.exp (-7209998542874754092888060186439/800000000000000000000000000000) (121877004866677502861/1000000000000000000000000) (60938502433338751431/500000000000000000000000) { parts := 10, inner := (-7209998542874754092888060186439/8000000000000000000000000000000), terms := 40, innerLo := (203030919563263701102065278093/500000000000000000000000000000), innerHi := (406061839126527402204130556187/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell453
