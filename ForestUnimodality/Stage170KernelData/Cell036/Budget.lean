import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell036.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell036
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(28540061780381397000539871871/250000000000000000000000000000)]
def R : ℚ := (365708962790697674418604651163/250000000000000000000000000000)
def D : ℚ := (6663680383/4000000000)
def vmax : ℚ := (860/3969)
def mlo : ℚ := (766521/6400)
def mhi : ℚ := (525/4)

def budgetExpression_lo : Expr := (.sub (.rat (5828711065618741900479179180330525490330259036675216257193/14400000000000000000000000000000000000000000000000000000000)) (.mul (.rat (476157519451819695177619/10000000000000000000000)) (.exp (-21876556695959728810250823126430791/1600000000000000000000000000000000) (288335156351946807/250000000000000000000000) (1153340625407787229/1000000000000000000000000) { parts := 14, inner := (-3125222385137104115750117589490113/3200000000000000000000000000000000), terms := 40, innerLo := (47072159928706358366857675871/125000000000000000000000000000), innerHi := (376577279429650866934861406969/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (420197755974099164320594981715776820001896238733888079/1080000000000000000000000000000000000000000000000000000)) (.mul (.rat (476157519451819695177619/10000000000000000000000)) (.exp (-599341297388009337011337309291/40000000000000000000000000000) (310981492961501231/1000000000000000000000000) (19436343310093827/62500000000000000000000) { parts := 15, inner := (-199780432462669779003779103097/200000000000000000000000000000), terms := 40, innerLo := (184141767430079303318000766393/500000000000000000000000000000), innerHi := (368283534860158606636001532787/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell036
