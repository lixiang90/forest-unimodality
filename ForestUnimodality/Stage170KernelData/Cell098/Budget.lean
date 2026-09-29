import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell098.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell098
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(113325767185493754314381385667/1000000000000000000000000000000)]
def R : ℚ := (527141393604651162790697674419/500000000000000000000000000000)
def D : ℚ := (177911323/100000000)
def vmax : ℚ := (5762/23409)
def mlo : ℚ := (30200373134328358208955223880596707/400000000000000000000000000000000)
def mhi : ℚ := (694608582089552238805970149253724261/8000000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (1160355653258170082826457222576128276491344887995980260489980910454552620862904287372935375800927/2774400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (26326605489090276535080193/500000000000000000000000)) (.exp (-3422480454735935818262345601391748313076077553408279701457198569/400000000000000000000000000000000000000000000000000000000000000) (38469722706397615207/200000000000000000000000) (48087153382997019009/250000000000000000000000) { parts := 9, inner := (-1140826818245311939420781867130582771025359184469426567152399523/1200000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (193237322394589621531843842351/500000000000000000000000000000), innerHi := (386474644789179243063687684703/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (456017135516457881013443353994091641503083151398504148497762237680697282044531451943504668270210383/1109760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (26326605489090276535080193/500000000000000000000000)) (.exp (-78717050458926523820033948832010211200749783728390433133515567087/8000000000000000000000000000000000000000000000000000000000000000) (26648478846135063281/500000000000000000000000) (53296957692270126563/1000000000000000000000000) { parts := 10, inner := (-78717050458926523820033948832010211200749783728390433133515567087/80000000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (23364164712755244927198936969/62500000000000000000000000000), innerHi := (74765327080816783767036598301/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell098
