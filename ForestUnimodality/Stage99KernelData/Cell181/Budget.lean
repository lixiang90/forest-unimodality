import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage99KernelData.Cell181.Parameters

namespace ForestUnimodality.Stage99KernelData.Cell181
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(42667396600759754979285784631/250000000000000000000000000000)]
def R : ℚ := (950083027272727272727272727273/500000000000000000000000000000)
def D : ℚ := (587751200888888888888888888889/250000000000000000000000000000)
def vmax : ℚ := (45/196)
def mlo : ℚ := (3073170731707317073170731707317/125000000000000000000000000000)
def mhi : ℚ := (63/2)
def alpha : ℚ := (8550747245454545454545454545457/19600000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.rat (873059304698902141702829730286276773089030204095323788621139960596947085049997828005321/3062500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (19637124872910498574185567/2500000000000000000000000)) (.exp (-131124194431603149448536801548923707263663359042318588845027/31250000000000000000000000000000000000000000000000000000000) (15056067365630252080407/1000000000000000000000000) (1882008420703781510051/125000000000000000000000) { parts := 5, inner := (-131124194431603149448536801548923707263663359042318588845027/156250000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (432058257562153445447924141943/1000000000000000000000000000000), innerHi := (54007282195269180680990517743/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (1598537686442070087120255439617101920318649691640329381111/7000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (19637124872910498574185567/2500000000000000000000000)) (.exp (-2688045985847864563695004431753/500000000000000000000000000000) (925172932261024774271/200000000000000000000000) (1156466165326280967839/250000000000000000000000) { parts := 6, inner := (-896015328615954854565001477251/1000000000000000000000000000000), terms := 40, innerLo := (102048234549295376375004200659/250000000000000000000000000000), innerHi := (408192938197181505500016802637/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage99KernelData.Cell181
