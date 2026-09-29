import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell195.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell195
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(99509328203628252009707765683/1000000000000000000000000000000)]
def alpha : ℚ := (188912430547372270686664626059/1000000000000000000000000000000)
def D : ℚ := (1603712378080563159953070003911/1000000000000000000000000000000)
def mlo : ℚ := (16693208430913348946135831381733/1000000000000000000000000000000)
def mhi : ℚ := (1339502332814930015552099533437/50000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (26225728817832018070543870370274869398722190104258885539974999505812154380987292801843/31250000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (798745385887373249289567/200000000000000000000000)) (.exp (-1661129956523330633080086542830030689498937160060262090468639/1000000000000000000000000000000000000000000000000000000000000) (5935132895618723966047/31250000000000000000000) (37984850531959833382701/200000000000000000000000) { parts := 2, inner := (-1661129956523330633080086542830030689498937160060262090468639/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (435802997534206006880820127973/1000000000000000000000000000000), innerHi := (217901498767103003440410063987/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (17921985749286890047301445418621523565188960515870873775905968069663079797676761120581/50000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (798745385887373249289567/200000000000000000000000)) (.exp (-133292977265606552808648986909435465654815190273300019642471/50000000000000000000000000000000000000000000000000000000000) (69539555438479834446497/1000000000000000000000000) (34769777719239917223249/500000000000000000000000) { parts := 3, inner := (-44430992421868850936216328969811821884938396757766673214157/50000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (102805727805876012047689490573/250000000000000000000000000000), innerHi := (411222911223504048190757962293/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell195
