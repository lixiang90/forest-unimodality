import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell310.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell310
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(27777344840565041738044346051/250000000000000000000000000000)]
def R : ℚ := (207144057/125000000)
def D : ℚ := (145571987196969696969696969697/62500000000000000000000000000)
def vmax : ℚ := (660/2809)
def mlo : ℚ := (17611484281965051745577136308589/312500000000000000000000000000)
def mhi : ℚ := (405064138485196190148274135097547/6250000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (471085426437508484314681937149720669826033910557771685634647628381350274678325095026206283/1371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (555311064861291541205901/40000000000000000000000)) (.exp (-489200272054334258853562274737095866308555035598856639532039/78125000000000000000000000000000000000000000000000000000000) (1907878318624593239189/1000000000000000000000000) (190787831862459323919/100000000000000000000000) { parts := 7, inner := (-489200272054334258853562274737095866308555035598856639532039/546875000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (51099570749779936090917025871/125000000000000000000000000000), innerHi := (408796565998239488727336206969/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (359166578387821595887032412631210806436907661146913262530225524850480872637551459851195057979/1097265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (555311064861291541205901/40000000000000000000000)) (.exp (-11251606257249687953631932318953204925096765818773702709236897/1562500000000000000000000000000000000000000000000000000000000) (9322733863250536273/12500000000000000000000) (745818709060042901841/1000000000000000000000000) { parts := 8, inner := (-11251606257249687953631932318953204925096765818773702709236897/12500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (406517418660098648614928896333/1000000000000000000000000000000), innerHi := (203258709330049324307464448167/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell310
