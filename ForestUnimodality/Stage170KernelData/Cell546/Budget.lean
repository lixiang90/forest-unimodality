import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell546.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell546
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(21780843788482408525269670883/200000000000000000000000000000)]
def R : ℚ := (1258218833/800000000)
def D : ℚ := (470607184888888888888888888889/200000000000000000000000000000)
def vmax : ℚ := (2520/10609)
def mlo : ℚ := (21049375029339949552647351896941/500000000000000000000000000000)
def mhi : ℚ := (44575147120955187287959098134699/1000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (89546740359152168595540701228533754373558625349155606515593550975801674443509229370144670667/265225000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6772332031334229895946919/500000000000000000000000)) (.exp (-458473149359235755919764573857164670029305126195684804468903/100000000000000000000000000000000000000000000000000000000000) (10206489927804932177471/1000000000000000000000000) (159476405121952065273/15625000000000000000000) { parts := 5, inner := (-458473149359235755919764573857164670029305126195684804468903/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (399737859197071200832173615533/1000000000000000000000000000000), innerHi := (199868929598535600416086807767/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (21747478326590138480691438154945547193778431289074574557714123670039109151143498128018887667/66306250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6772332031334229895946919/500000000000000000000000)) (.exp (-970884316290146306653619097579887093350676701170842932269217/200000000000000000000000000000000000000000000000000000000000) (7793840151491640232637/1000000000000000000000000) (3896920075745820116319/500000000000000000000000) { parts := 5, inner := (-970884316290146306653619097579887093350676701170842932269217/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (189373978489085578215222425351/500000000000000000000000000000), innerHi := (378747956978171156430444850703/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell546
