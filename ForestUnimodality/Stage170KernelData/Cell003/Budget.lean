import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell003.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell003
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(62048118741949707749426215457/500000000000000000000000000000)]
def R : ℚ := (631431/500000)
def D : ℚ := (1456173623456790123456790123457/1000000000000000000000000000000)
def vmax : ℚ := (234/1225)
def mlo : ℚ := (591451388888888888888888888888887537/4000000000000000000000000000000000)
def mhi : ℚ := (1225/8)

def budgetExpression_lo : Expr := (.sub (.rat (91665726760895457175371464905446808569546861907266339192464233851927389606214716866559087429503237/196000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (94999974850933347170212073/100000000000000000000000)) (.exp (-36698446007868851800770009335119589728948807410878423636804059409/2000000000000000000000000000000000000000000000000000000000000000) (537036379723329/50000000000000000000000) (10740727594466581/1000000000000000000000000) { parts := 19, inner := (-36698446007868851800770009335119589728948807410878423636804059409/38000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (380698110377109030021714738251/1000000000000000000000000000000), innerHi := (95174527594277257505428684563/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (36739297729235781350541277472847586948547135561597981608261/80000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (94999974850933347170212073/100000000000000000000000)) (.exp (-3040357818355535679721884557393/160000000000000000000000000000) (5590280541509773/1000000000000000000000000) (2795140270754887/500000000000000000000000) { parts := 20, inner := (-3040357818355535679721884557393/3200000000000000000000000000000), terms := 40, innerLo := (386697781173111991910704844003/1000000000000000000000000000000), innerHi := (96674445293277997977676211001/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell003
