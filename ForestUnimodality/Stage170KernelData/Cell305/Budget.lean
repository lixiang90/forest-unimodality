import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell305.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell305
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(55011040388790565111692160211/500000000000000000000000000000)]
def R : ℚ := (321940661/200000000)
def D : ℚ := (1170408068682170542635658914729/500000000000000000000000000000)
def vmax : ℚ := (10320/43681)
def mlo : ℚ := (1134366821189930220741284823863897/20000000000000000000000000000000)
def mhi : ℚ := (26090436887368395077049550948869631/400000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (631215917987654974547444898037007742062071037897847703123714348943122795784574225491395784683033/1747240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (152080566152852423300601/10000000000000000000000)) (.exp (-62402699016183216424794472659937113793796177460794299782802267/10000000000000000000000000000000000000000000000000000000000000) (1949329324698071802259/1000000000000000000000000) (97466466234903590113/50000000000000000000000) { parts := 7, inner := (-62402699016183216424794472659937113793796177460794299782802267/70000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (205026854807462744821327650239/500000000000000000000000000000), innerHi := (410053709614925489642655300479/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (239892816522354282827146722142903891780166711664842765520970474636297759170069746459468265062121697/698896000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (152080566152852423300601/10000000000000000000000)) (.exp (-1435262077372213977770272871178553617257312081598268895004452141/200000000000000000000000000000000000000000000000000000000000000) (38224164629813718457/50000000000000000000000) (764483292596274369141/1000000000000000000000000) { parts := 8, inner := (-1435262077372213977770272871178553617257312081598268895004452141/1600000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (203887689396163461090631705461/500000000000000000000000000000), innerHi := (407775378792326922181263410923/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell305
