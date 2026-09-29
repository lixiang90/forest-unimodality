import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell142.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell142
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(49406255423319348889116369021/500000000000000000000000000000)]
def alpha : ℚ := (85880049892071407937509287683/500000000000000000000000000000)
def D : ℚ := (1480559545488693189361419657477/1000000000000000000000000000000)
def mlo : ℚ := (8167093979312173989921315533551/500000000000000000000000000000)
def mhi : ℚ := (44198390946865882768985942887453/2000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (547454798724532452990907610878495177968365084509338468728216336866756222169661020188301/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2645269270665430383360217/500000000000000000000000)) (.exp (-403505531208150898389071871401441853450719761430510422523571/250000000000000000000000000000000000000000000000000000000000) (7963410232522656201119/40000000000000000000000) (24885656976633300628497/125000000000000000000000) { parts := 2, inner := (-403505531208150898389071871401441853450719761430510422523571/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (446189708322666721980800602331/1000000000000000000000000000000), innerHi := (111547427080666680495200150583/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (2549987854826180352706391302559784586565622727006399844668558466980162637456131745327899/4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2645269270665430383360217/500000000000000000000000)) (.exp (-2183676992420581332458506598172535010221472230926291818793513/1000000000000000000000000000000000000000000000000000000000000) (112626641029503067056927/1000000000000000000000000) (3519582532171970845529/31250000000000000000000) { parts := 3, inner := (-727892330806860444152835532724178336740490743642097272931171/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (241462882979850721039392537987/500000000000000000000000000000), innerHi := (19317030638388057683151403039/40000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell142
