import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage130KernelData.Cell008.Parameters

namespace ForestUnimodality.Stage130KernelData.Cell008
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(28540061780381397000539871871/250000000000000000000000000000), (193238010099170504361179844997/1000000000000000000000000000000)]
def R : ℚ := (365708962790697674418604651163/250000000000000000000000000000)
def D : ℚ := (6663680383/4000000000)
def vmax : ℚ := (860/3969)
def mlo : ℚ := (2079/40)
def mhi : ℚ := (1071/16)
def alpha : ℚ := (2246497914285714285714285714287/7087500000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (12558363651523945630630351488174351782644927104764576423/31250000000000000000000000000000000000000000000000000000)) (.mul (.rat (11980420349021159154290217/10000000000000000000000000)) (.exp (-59334788441412924364122393619809/10000000000000000000000000000000) (2649249612594998444991/1000000000000000000000000) (41394525196796850703/15625000000000000000000) { parts := 6, inner := (-19778262813804308121374131206603/20000000000000000000000000000000), terms := 40, innerLo := (74396152430488140542264331299/200000000000000000000000000000), innerHi := (23248797634527543919457603531/62500000000000000000000000000) }))) (.mul (.rat (65004056899802389324349861/10000000000000000000000000)) (.exp (-401741822996175478566892897748763/40000000000000000000000000000000) (21732694865962073073/500000000000000000000000) (43465389731924146147/1000000000000000000000000) { parts := 11, inner := (-36521983908743225324262990704433/40000000000000000000000000000000), terms := 40, innerLo := (401298556924056701013311604841/1000000000000000000000000000000), innerHi := (200649278462028350506655802421/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (4784748055449493115938236201286662992195871538818115127/12500000000000000000000000000000000000000000000000000000)) (.mul (.rat (11980420349021159154290217/10000000000000000000000000)) (.exp (-30566406166788476187578202773841/4000000000000000000000000000000) (240029500780620647399/500000000000000000000000) (480059001561241294799/1000000000000000000000000) { parts := 8, inner := (-30566406166788476187578202773841/32000000000000000000000000000000), terms := 40, innerLo := (192367557838331604655921401833/500000000000000000000000000000), innerHi := (384735115676663209311842803667/1000000000000000000000000000000) }))) (.mul (.rat (65004056899802389324349861/10000000000000000000000000)) (.exp (-206957908816211610170823613991787/16000000000000000000000000000000) (75388944012869147/31250000000000000000000) (482489241682362541/200000000000000000000000) { parts := 13, inner := (-206957908816211610170823613991787/208000000000000000000000000000000), terms := 40, innerLo := (184863580838279528034676124787/500000000000000000000000000000), innerHi := (14789086467062362242774089983/40000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_hi_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms (∅ : Finset ℤ)
    row.A row.B row.dδ row.dM alpha varianceIntercept D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ)) (fun _ => 0) (fun _ => 0)
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage130KernelData.Cell008
