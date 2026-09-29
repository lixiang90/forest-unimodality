import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell042.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell042
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(29810624092422477535348571433/250000000000000000000000000000)]
def R : ℚ := (3803687/2500000)
def D : ℚ := (3383039/2000000)
def vmax : ℚ := (2/9)
def mlo : ℚ := (345/4)
def mhi : ℚ := (1587/16)

def budgetExpression_lo : Expr := (.sub (.rat (1865278262113722012555497436324306073/4800000000000000000000000000000000000)) (.mul (.rat (95327986829993236028713/8000000000000000000000)) (.exp (-2056933062377150949939051428877/200000000000000000000000000000) (1366112918311162899/40000000000000000000000) (8538205739444768119/250000000000000000000000) { parts := 11, inner := (-2056933062377150949939051428877/2200000000000000000000000000000), terms := 40, innerLo := (78519562121248060284825256351/200000000000000000000000000000), innerHi := (98149452651560075356031570439/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (35406926944741140308116980357824914679/96000000000000000000000000000000000000)) (.mul (.rat (95327986829993236028713/8000000000000000000000)) (.exp (-47309460434674471848598182864171/4000000000000000000000000000000) (3650989653307793383/500000000000000000000000) (7301979306615586767/1000000000000000000000000) { parts := 12, inner := (-15769820144891490616199394288057/16000000000000000000000000000000), terms := 40, innerLo := (373210095552292024639678925811/1000000000000000000000000000000), innerHi := (93302523888073006159919731453/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell042
