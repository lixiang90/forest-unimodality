import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell416.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell416
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(21780843788482408525269670883/200000000000000000000000000000)]
def R : ℚ := (1258218833/800000000)
def D : ℚ := (470607184888888888888888888889/200000000000000000000000000000)
def vmax : ℚ := (2520/10609)
def mlo : ℚ := (44575147120955187287959098134699/1000000000000000000000000000000)
def mhi : ℚ := (12381985311376440913321971704083/250000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (46385061582857822598550918226709269421969339723434662983342814395057023896723416187506442169/132612500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (14324497417138575272588241/1000000000000000000000000)) (.exp (-970884316290146306653619097579887093350676701170842932269217/200000000000000000000000000000000000000000000000000000000000) (7793840151491640232637/1000000000000000000000000) (3896920075745820116319/500000000000000000000000) { parts := 5, inner := (-970884316290146306653619097579887093350676701170842932269217/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (189373978489085578215222425351/500000000000000000000000000000), innerHi := (378747956978171156430444850703/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (87333308597753238627621964390217833181630657720169233298368371878735940551563919777459275297/265225000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (14324497417138575272588241/1000000000000000000000000)) (.exp (-269690087858373974070449749327745204772755279080316077315289/50000000000000000000000000000000000000000000000000000000000) (56808284338562781097/12500000000000000000000) (4544662747085022487761/1000000000000000000000000) { parts := 6, inner := (-269690087858373974070449749327745204772755279080316077315289/300000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (406989879668559471827111580413/1000000000000000000000000000000), innerHi := (203494939834279735913555790207/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell416
