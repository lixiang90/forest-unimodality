import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell044.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell044
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(29810624092422477535348571433/250000000000000000000000000000)]
def R : ℚ := (3803687/2500000)
def D : ℚ := (3383039/2000000)
def vmax : ℚ := (2/9)
def mlo : ℚ := (36501/320)
def mhi : ℚ := (839523/6400)

def budgetExpression_lo : Expr := (.sub (.rat (245087362596326818242553980116432720227/640000000000000000000000000000000000000)) (.mul (.rat (99544887670713990246440517/1000000000000000000000000)) (.exp (-1088117589997512852517758205875933/80000000000000000000000000000000) (1238673046698214171/1000000000000000000000000) (309668261674553543/250000000000000000000000) { parts := 14, inner := (-155445369999644693216822600839419/160000000000000000000000000000000), terms := 40, innerLo := (94625534027805503725075413887/250000000000000000000000000000), innerHi := (378502136111222014900301655549/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (9276835658899651839868708405319830397317/25600000000000000000000000000000000000000)) (.mul (.rat (99544887670713990246440517/1000000000000000000000000)) (.exp (-25026704569942795607908438735146459/1600000000000000000000000000000000) (40256887998150631/250000000000000000000000) (6441102079704101/40000000000000000000000) { parts := 16, inner := (-25026704569942795607908438735146459/25600000000000000000000000000000000), terms := 40, innerLo := (376210802682351368986240803907/1000000000000000000000000000000), innerHi := (94052700670587842246560200977/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell044
