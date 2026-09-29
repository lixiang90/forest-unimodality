import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell544.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell544
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(26642894181863998810416339533/250000000000000000000000000000)]
def R : ℚ := (1199131211/800000000)
def D : ℚ := (2379308466666666666666666666667/1000000000000000000000000000000)
def vmax : ℚ := (6/25)
def mlo : ℚ := (21237212827920694231148535443559/500000000000000000000000000000)
def mhi : ℚ := (22486460641327793891804331646121/500000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (3330712408994087530097333442988565083994534781324227017307657719094379122699824156862499/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (15505068553144651488651107/1000000000000000000000000)) (.exp (-565820814092015745280429689776954645783888973464995301917947/125000000000000000000000000000000000000000000000000000000000) (1352219375666219235019/125000000000000000000000) (10817755005329753880153/1000000000000000000000000) { parts := 5, inner := (-565820814092015745280429689776954645783888973464995301917947/625000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (101103790238123227457510909847/250000000000000000000000000000), innerHi := (404415160952492909830043639389/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (16261190658053851703437226560597721332978085270266576131871899105331356910760211822900997/50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (15505068553144651488651107/1000000000000000000000000)) (.exp (-599104391391546083238102024469708847625828953080933138401493/125000000000000000000000000000000000000000000000000000000000) (8288923851299283715177/1000000000000000000000000) (4144461925649641857589/500000000000000000000000) { parts := 5, inner := (-599104391391546083238102024469708847625828953080933138401493/625000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (383441954745402538391602255709/1000000000000000000000000000000), innerHi := (38344195474540253839160225571/100000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell544
