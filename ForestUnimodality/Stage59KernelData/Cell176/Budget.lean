import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell176.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell176
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(50418343167935485629757592137/500000000000000000000000000000)]
def alpha : ℚ := (87035444987718057996086691401/500000000000000000000000000000)
def D : ℚ := (1506340860556218218343901060959/1000000000000000000000000000000)
def mlo : ℚ := (17004529336080921348549671021663/1000000000000000000000000000000)
def mhi : ℚ := (27396186152574817728218914423791/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (613049243777180431700990852099696616392212649834005929549433144589419560996975325049/312500000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1047038857776664322329907/100000000000000000000000)) (.exp (-857340195475754060267408842136208878669541151300975645463831/500000000000000000000000000000000000000000000000000000000000) (180021247939273665563383/1000000000000000000000000) (22502655992409208195423/125000000000000000000000) { parts := 2, inner := (-857340195475754060267408842136208878669541151300975645463831/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (424289108909566126236821459251/1000000000000000000000000000000), innerHi := (106072277227391531559205364813/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (230585330893166908568199619102994223654611123202608533318520811799764747449716274793/312500000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1047038857776664322329907/100000000000000000000000)) (.exp (-1381270314933159319319714245663922893510641148781678947331367/500000000000000000000000000000000000000000000000000000000000) (12626234299526234309423/200000000000000000000000) (15782792874407792886779/250000000000000000000000) { parts := 3, inner := (-460423438311053106439904748554640964503547049593892982443789/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (9954542187343817789371733109/25000000000000000000000000000), innerHi := (398181687493752711574869324361/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_hi_positive : 0 < budget mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < budget m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms row.fixedIndices
    row.A row.B row.dδ row.dM alpha varianceIntercept D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell176
