import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell035.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell035
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(28540061780381397000539871871/250000000000000000000000000000)]
def R : ℚ := (365708962790697674418604651163/250000000000000000000000000000)
def D : ℚ := (6663680383/4000000000)
def vmax : ℚ := (860/3969)
def mlo : ℚ := (33327/320)
def mhi : ℚ := (766521/6400)

def budgetExpression_lo : Expr := (.sub (.rat (147105869115020592469311902540806181859665066186041716244699/360000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2524387406675342226947123/62500000000000000000000)) (.exp (-951154638954770817836992309844817/80000000000000000000000000000000) (3431269778447631063/500000000000000000000000) (6862539556895262127/1000000000000000000000000) { parts := 12, inner := (-317051546318256939278997436614939/320000000000000000000000000000000), terms := 40, innerLo := (46410589494498258407256301233/125000000000000000000000000000), innerHi := (74256943191197213451610081973/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (2785304138802139518402325449374155428826984022278959473628077/7200000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2524387406675342226947123/62500000000000000000000)) (.exp (-21876556695959728810250823126430791/1600000000000000000000000000000000) (288335156351946807/250000000000000000000000) (1153340625407787229/1000000000000000000000000) { parts := 14, inner := (-3125222385137104115750117589490113/3200000000000000000000000000000000), terms := 40, innerLo := (47072159928706358366857675871/125000000000000000000000000000), innerHi := (376577279429650866934861406969/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell035
