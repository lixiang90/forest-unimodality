import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage80KernelData.Cell001.Parameters

namespace ForestUnimodality.Stage80KernelData.Cell001
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(170234194167175226529232842337/1000000000000000000000000000000)]
def R : ℚ := (256966306796116504854368932039/200000000000000000000000000000)
def D : ℚ := (747246585829072315558802045289/500000000000000000000000000000)
def vmax : ℚ := (3811/19600)
def mlo : ℚ := (37837837837837837837837837837837/1000000000000000000000000000000)
def mhi : ℚ := (47297297297297297297297297297297/1000000000000000000000000000000)
def alpha : ℚ := (979298595200000000000000000000629/3920000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.rat (1787942903442202686570312733149033303254657641638599564442324034306326947769162747501361391/3920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (19701037968261450039619831/5000000000000000000000000)) (.exp (-6441293833352576138943945385724181695675157231566961994105069/1000000000000000000000000000000000000000000000000000000000000) (1594342532024689686939/1000000000000000000000000) (79717126601234484347/50000000000000000000000) { parts := 7, inner := (-920184833336082305563420769389168813667879604509565999157867/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (199222694143806983710143751411/500000000000000000000000000000), innerHi := (398445388287613967420287502823/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (68950323598917204046667910631448203334112245975405129143225820089878941428107850130810227/156800000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (19701037968261450039619831/5000000000000000000000000)) (.exp (-8051617291690720173679931732155354795239571920878599417263089/1000000000000000000000000000000000000000000000000000000000000) (159293129347629414901/500000000000000000000000) (318586258695258829803/1000000000000000000000000) { parts := 9, inner := (-8051617291690720173679931732155354795239571920878599417263089/9000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (408761205319312489119349709841/1000000000000000000000000000000), innerHi := (204380602659656244559674854921/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage80KernelData.Cell001
