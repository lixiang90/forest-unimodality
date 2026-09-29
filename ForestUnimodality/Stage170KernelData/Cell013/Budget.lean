import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell013.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell013
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(101962848925931214867995971687/1000000000000000000000000000000)]
def R : ℚ := (332518930693069306930693069307/250000000000000000000000000000)
def D : ℚ := (1557844460223537146614069690993/1000000000000000000000000000000)
def vmax : ℚ := (3939/19600)
def mlo : ℚ := (2064102564102564102564102564102547/20000000000000000000000000000000)
def mhi : ℚ := (47474358974358974358974358974358581/400000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (8911723462244322061361361204255830311105250571268628437091829987930243148784864764896158068887/19600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (94495194847697323581314777/10000000000000000000000000)) (.exp (-210461777911216994791632710789831589507173497535376488376586789/20000000000000000000000000000000000000000000000000000000000000) (26907946782488294789/1000000000000000000000000) (2690794678248829479/100000000000000000000000) { parts := 11, inner := (-210461777911216994791632710789831589507173497535376488376586789/220000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (76835972429126312372698880351/200000000000000000000000000000), innerHi := (96044965536407890465873600439/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (3400657012886131814838560384700278595680190552627923782450675291764245248606693869184671563720223/7840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (94495194847697323581314777/10000000000000000000000000)) (.exp (-4840620891957990880207552348166126558664990443313659232661496147/400000000000000000000000000000000000000000000000000000000000000) (2775445146562765827/500000000000000000000000) (1110178058625106331/200000000000000000000000) { parts := 13, inner := (-372355453227537760015965565243548196820383880254896864050884319/400000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (197101626317179534076824682793/500000000000000000000000000000), innerHi := (394203252634359068153649365587/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell013
