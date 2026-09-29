import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage99KernelData.Cell021.Parameters

namespace ForestUnimodality.Stage99KernelData.Cell021
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 2 → ℚ := ![(34092103765847650047192805959/250000000000000000000000000000), (221707449158650560705996841099/1000000000000000000000000000000)]
def R : ℚ := (9850373/10000000)
def D : ℚ := (90810693/50000000)
def vmax : ℚ := (5696/23409)
def mlo : ℚ := (3825/128)
def mhi : ℚ := (5049/128)
def alpha : ℚ := (876683197/3657656250)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.sub (.rat (18392740236222006740243986236413399077/40800000000000000000000000000000000000)) (.mul (.rat (6532540578872093384177333/2000000000000000000000000)) (.exp (-5216091876174690457220499311727/1280000000000000000000000000000) (4247748762278205617059/250000000000000000000000) (16990995049112822468237/1000000000000000000000000) { parts := 5, inner := (-5216091876174690457220499311727/6400000000000000000000000000000), terms := 40, innerLo := (442632973030685633950546351241/1000000000000000000000000000000), innerHi := (221316486515342816975273175621/500000000000000000000000000000) }))) (.mul (.rat (2851796347292569677733809/200000000000000000000000)) (.exp (-33921239721273535788017516688147/5120000000000000000000000000000) (1326459212510017759083/1000000000000000000000000) (331614803127504439771/250000000000000000000000) { parts := 7, inner := (-33921239721273535788017516688147/35840000000000000000000000000000), terms := 40, innerLo := (388111285623616730223223059529/1000000000000000000000000000000), innerHi := (38811128562361673022322305953/100000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.sub (.rat (133866648395062227050949951689405202347/340000000000000000000000000000000000000)) (.mul (.rat (6532540578872093384177333/2000000000000000000000000)) (.exp (-172131031913764785088276477286991/32000000000000000000000000000000) (4611995061796690496697/1000000000000000000000000) (2305997530898345248349/500000000000000000000000) { parts := 6, inner := (-57377010637921595029425492428997/64000000000000000000000000000000), terms := 40, innerLo := (203994352003719267074118849089/500000000000000000000000000000), innerHi := (407988704007438534148237698179/1000000000000000000000000000000) }))) (.mul (.rat (2851796347292569677733809/200000000000000000000000)) (.exp (-1119400910802026681004578050708851/128000000000000000000000000000000) (31840944672208580893/200000000000000000000000) (79602361680521452233/500000000000000000000000) { parts := 9, inner := (-124377878978002964556064227856539/128000000000000000000000000000000), terms := 40, innerLo := (378438319590200893094753351381/1000000000000000000000000000000), innerHi := (189219159795100446547376675691/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage99KernelData.Cell021
