import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell034.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell034
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(28540061780381397000539871871/250000000000000000000000000000)]
def R : ℚ := (365708962790697674418604651163/250000000000000000000000000000)
def D : ℚ := (6663680383/4000000000)
def vmax : ℚ := (860/3969)
def mlo : ℚ := (1449/16)
def mhi : ℚ := (33327/320)

def budgetExpression_lo : Expr := (.sub (.rat (247885653412746048557747112863387499039983601773593808941/600000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6372182307757319641439153/500000000000000000000000)) (.exp (-41354549519772644253782274341079/4000000000000000000000000000000) (8089596204448994351/250000000000000000000000) (6471676963559195481/200000000000000000000000) { parts := 11, inner := (-41354549519772644253782274341079/44000000000000000000000000000000), terms := 40, innerLo := (97669056800820901362155483893/250000000000000000000000000000), innerHi := (390676227203283605448621935573/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (4716414394096382655151429555038428610732122840792657605643/12000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6372182307757319641439153/500000000000000000000000)) (.exp (-951154638954770817836992309844817/80000000000000000000000000000000) (3431269778447631063/500000000000000000000000) (6862539556895262127/1000000000000000000000000) { parts := 12, inner := (-317051546318256939278997436614939/320000000000000000000000000000000), terms := 40, innerLo := (46410589494498258407256301233/125000000000000000000000000000), innerHi := (74256943191197213451610081973/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell034
