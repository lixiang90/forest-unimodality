import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell325.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell325
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(58388493209979575014980350259/500000000000000000000000000000)]
def R : ℚ := (1967611776744186046511627906977/1000000000000000000000000000000)
def D : ℚ := (566455824682926829268292682927/200000000000000000000000000000)
def vmax : ℚ := (902/3969)
def mlo : ℚ := (47869197186168414580227095924067/1000000000000000000000000000000)
def mhi : ℚ := (1100991535281873535345223206253541/20000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (4720245836458415396449942379647645938364830439537899387056219575396511924018709602371894481/16537500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (98089661816413240558176767/10000000000000000000000000)) (.exp (-2795010294871767852998624641218543647225345284229914927783353/500000000000000000000000000000000000000000000000000000000000) (933737740553484529467/250000000000000000000000) (3734950962213938117869/1000000000000000000000000) { parts := 6, inner := (-931670098290589284332874880406181215741781761409971642594451/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (393895316838355212809964304647/1000000000000000000000000000000), innerHi := (49236914604794401601245538081/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (3501063412555118374350173074302056869848501424066809566270947782764596080645462920975482030033/13230000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (98089661816413240558176767/10000000000000000000000000)) (.exp (-64285236782050660618968366748026503886182941537288043339017119/10000000000000000000000000000000000000000000000000000000000000) (1614833088851232951421/1000000000000000000000000) (807416544425616475711/500000000000000000000000) { parts := 7, inner := (-64285236782050660618968366748026503886182941537288043339017119/70000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (399172938784777663142994905741/1000000000000000000000000000000), innerHi := (199586469392388831571497452871/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell325
