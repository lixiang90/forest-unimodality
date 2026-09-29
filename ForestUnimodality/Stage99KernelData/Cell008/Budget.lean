import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage99KernelData.Cell008.Parameters

namespace ForestUnimodality.Stage99KernelData.Cell008
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(28540061780381397000539871871/250000000000000000000000000000), (193352433549996347728434978377/1000000000000000000000000000000)]
def R : ℚ := (365708962790697674418604651163/250000000000000000000000000000)
def D : ℚ := (6663680383/4000000000)
def vmax : ℚ := (860/3969)
def mlo : ℚ := (315/8)
def mhi : ℚ := (2079/40)
def alpha : ℚ := (2246497914285714285714285714287/7087500000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (23402403761609162730127394681717760609658778187338940161/60000000000000000000000000000000000000000000000000000000)) (.mul (.rat (26882710551603911097728883/50000000000000000000000000)) (.exp (-1798023892164028011034011927873/400000000000000000000000000000) (2791003441020414896557/250000000000000000000000) (11164013764081659586229/1000000000000000000000000) { parts := 5, inner := (-1798023892164028011034011927873/2000000000000000000000000000000), terms := 40, innerLo := (101742892752036039955213191461/250000000000000000000000000000), innerHi := (81394314201628831964170553169/200000000000000000000000000000) }))) (.mul (.rat (61730103462258423263619989/10000000000000000000000000)) (.exp (-12181203313649769906891403637751/1600000000000000000000000000000) (246931583004302048897/500000000000000000000000) (98772633201720819559/200000000000000000000000) { parts := 8, inner := (-12181203313649769906891403637751/12800000000000000000000000000000), terms := 40, innerLo := (38610091383532518282166766393/100000000000000000000000000000), innerHi := (386100913835325182821667663931/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (188804712141102349427293355174020366706246560060728341771/500000000000000000000000000000000000000000000000000000000)) (.mul (.rat (26882710551603911097728883/50000000000000000000000000)) (.exp (-59334788441412924364122393619809/10000000000000000000000000000000) (2649249612594998444991/1000000000000000000000000) (41394525196796850703/15625000000000000000000) { parts := 6, inner := (-19778262813804308121374131206603/20000000000000000000000000000000), terms := 40, innerLo := (74396152430488140542264331299/200000000000000000000000000000), innerHi := (23248797634527543919457603531/62500000000000000000000000000) }))) (.mul (.rat (61730103462258423263619989/10000000000000000000000000)) (.exp (-401979709350442406927416320045783/40000000000000000000000000000000) (4320766129004024507/100000000000000000000000) (43207661290040245071/1000000000000000000000000) { parts := 11, inner := (-36543609940949309720674210913253/40000000000000000000000000000000), terms := 40, innerLo := (200540826588012904973217981751/500000000000000000000000000000), innerHi := (401081653176025809946435963503/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage99KernelData.Cell008
