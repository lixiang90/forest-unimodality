import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell160.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell160
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(99807142772223361460760629077/1000000000000000000000000000000)]
def alpha : ℚ := (21681199150021055145140047289/125000000000000000000000000000)
def D : ℚ := (59721460281633705932932072227/40000000000000000000000000000)
def mlo : ℚ := (16175005368262830148164054112089/1000000000000000000000000000000)
def mhi : ℚ := (85483714032639038007300837449/3906250000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (829178572627792785538642922400491736033006184689203647705540572500996237662256826525473/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3970060452056485722494017/500000000000000000000000)) (.exp (-1614381070131687599045461865252958255205709000413796310611853/1000000000000000000000000000000000000000000000000000000000000) (199013807920085148200681/1000000000000000000000000) (99506903960042574100341/500000000000000000000000) { parts := 2, inner := (-1614381070131687599045461865252958255205709000413796310611853/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (108913485512467631314664887/244140625000000000000000000), innerHi := (446109636659067417864867377153/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (7593737620408245587513606228077351148613255194548827916532286834164138483203906197387/7812500000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3970060452056485722494017/500000000000000000000000)) (.exp (-8531885251155518101572983203312991653693492470790159904573/3906250000000000000000000000000000000000000000000000000000) (112571959221308106350759/1000000000000000000000000) (2814298980532702658769/25000000000000000000000) { parts := 3, inner := (-8531885251155518101572983203312991653693492470790159904573/11718750000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (120711899392902194711931024671/250000000000000000000000000000), innerHi := (96569519514321755769544819737/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell160
