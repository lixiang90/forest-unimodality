import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell039.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell039
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(7293835734100484316986055413/62500000000000000000000000000)]
def R : ℚ := (186476298823529411764705882353/125000000000000000000000000000)
def D : ℚ := (1679747933135038667459845330161/1000000000000000000000000000000)
def vmax : ℚ := (3485/15876)
def mlo : ℚ := (20321341463414634146341463414633927/200000000000000000000000000000000)
def mhi : ℚ := (467390853658536585365853658536580321/4000000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (2324522170196068068944680085470401854958422052142527388204184205590762881930477096828595632848503/5880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (10097440805176416844801679/250000000000000000000000)) (.exp (-148220526530711488312313578505517302598420566691330179131796851/12500000000000000000000000000000000000000000000000000000000000) (1771052627086084507/250000000000000000000000) (7084210508344338029/1000000000000000000000000) { parts := 12, inner := (-148220526530711488312313578505517302598420566691330179131796851/150000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (74453928374498917959927445037/200000000000000000000000000000), innerHi := (186134820936247294899818612593/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (882410902777556180622545568470880552518010358158605865461125615510088600679928584574120415944437887/2352000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (10097440805176416844801679/250000000000000000000000)) (.exp (-3409072110206364231183212305626897959763673033900594120031327573/250000000000000000000000000000000000000000000000000000000000000) (1196286430379182339/1000000000000000000000000) (59814321518959117/50000000000000000000000) { parts := 14, inner := (-3409072110206364231183212305626897959763673033900594120031327573/3500000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (377561955618347943207711575513/1000000000000000000000000000000), innerHi := (188780977809173971603855787757/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell039
