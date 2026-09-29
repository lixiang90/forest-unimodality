import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell547.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell547
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(55011040388790565111692160211/500000000000000000000000000000)]
def R : ℚ := (321940661/200000000)
def D : ℚ := (1170408068682170542635658914729/500000000000000000000000000000)
def vmax : ℚ := (10320/43681)
def mlo : ℚ := (41922252087453942940438786968883/1000000000000000000000000000000)
def mhi : ℚ := (8877653383225540857975272534587/200000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (1466445306535264351887994893433566323977771159079921029492549647404663776144525809855921538477/4368100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6321967107981198985555693/500000000000000000000000)) (.exp (-2306186702771988433090230511345493779853800413661979107714313/500000000000000000000000000000000000000000000000000000000000) (9928226614506248437891/1000000000000000000000000) (2482056653626562109473/250000000000000000000000) { parts := 5, inner := (-2306186702771988433090230511345493779853800413661979107714313/2500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (198767026405330023005789367859/500000000000000000000000000000), innerHi := (397534052810660046011578735719/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (15015209596418547398659243744621179578212457071047961196142536804746714053897457073279500451/45980000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6321967107981198985555693/500000000000000000000000)) (.exp (-488368948822303432889695872990811094687162308664479242717857/100000000000000000000000000000000000000000000000000000000000) (7569036576766732825881/1000000000000000000000000) (3784518288383366412941/500000000000000000000000) { parts := 5, inner := (-488368948822303432889695872990811094687162308664479242717857/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (188268700572656673680437823767/500000000000000000000000000000), innerHi := (75307480229062669472175129507/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell547
