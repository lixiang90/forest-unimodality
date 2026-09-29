import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell417.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell417
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(55011040388790565111692160211/500000000000000000000000000000)]
def R : ℚ := (321940661/200000000)
def D : ℚ := (1170408068682170542635658914729/500000000000000000000000000000)
def vmax : ℚ := (10320/43681)
def mlo : ℚ := (8877653383225540857975272534587/200000000000000000000000000000)
def mhi : ℚ := (49320296573475226988751514081039/1000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (15974121329474895154566807087535718568537682697894703223305964692306828586776632898618209377/45980000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6680629778570818189109559/500000000000000000000000)) (.exp (-488368948822303432889695872990811094687162308664479242717857/100000000000000000000000000000000000000000000000000000000000) (7569036576766732825881/1000000000000000000000000) (3784518288383366412941/500000000000000000000000) { parts := 5, inner := (-488368948822303432889695872990811094687162308664479242717857/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (188268700572656673680437823767/500000000000000000000000000000), innerHi := (75307480229062669472175129507/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (1433316418196218790210150101706180305620179813294377672519236132144677320392579402455069120319/4368100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6680629778570818189109559/500000000000000000000000)) (.exp (-2713160826790574627164977072171178860599833802643230425339229/500000000000000000000000000000000000000000000000000000000000) (1099812008990198086527/250000000000000000000000) (4399248035960792346109/1000000000000000000000000) { parts := 6, inner := (-2713160826790574627164977072171178860599833802643230425339229/3000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (80957993734483044158912170541/200000000000000000000000000000), innerHi := (202394984336207610397280426353/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell417
