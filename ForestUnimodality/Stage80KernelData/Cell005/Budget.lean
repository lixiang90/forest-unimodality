import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage80KernelData.Cell005.Parameters

namespace ForestUnimodality.Stage80KernelData.Cell005
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(22842055492324579001728439867/125000000000000000000000000000)]
def R : ℚ := (1379818912359550561797752808989/1000000000000000000000000000000)
def D : ℚ := (100571575328707085463842220599/62500000000000000000000000000)
def vmax : ℚ := (3293/15876)
def mlo : ℚ := (17027027027027027027027027027027/500000000000000000000000000000)
def mhi : ℚ := (42567567567567567567567567567567/1000000000000000000000000000000)
def alpha : ℚ := (4543743678400000000000000000000777/15876000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.rat (21046105499278701022803023179764698317167425713572141415693113831723807345161984944205901391/49612500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (49440900060007306748843803/10000000000000000000000000)) (.exp (-388932296220661750569970732870539923187689396632999953285409/62500000000000000000000000000000000000000000000000000000000) (1983451560505179530891/1000000000000000000000000) (495862890126294882723/250000000000000000000000) { parts := 7, inner := (-55561756602951678652852961838648560455384199518999993326487/62500000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (411071503301831022723796449521/1000000000000000000000000000000), innerHi := (205535751650915511361898224761/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (7755923173531087426530692286654624334214858573682817799804804864955567677363055889771978003/18900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (49440900060007306748843803/10000000000000000000000000)) (.exp (-972330740551654376424926832176338386941477329292999018993589/125000000000000000000000000000000000000000000000000000000000) (104644644520409387979/250000000000000000000000) (418578578081637551917/1000000000000000000000000) { parts := 8, inner := (-972330740551654376424926832176338386941477329292999018993589/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (378200522750717959647752843809/1000000000000000000000000000000), innerHi := (37820052275071795964775284381/100000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

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
end ForestUnimodality.Stage80KernelData.Cell005
