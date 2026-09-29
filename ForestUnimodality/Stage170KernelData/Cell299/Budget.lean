import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell299.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell299
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(21780843788482408525269670883/200000000000000000000000000000)]
def R : ℚ := (1258218833/800000000)
def D : ℚ := (470607184888888888888888888889/200000000000000000000000000000)
def vmax : ℚ := (2520/10609)
def mlo : ℚ := (12381985311376440913321971704083/250000000000000000000000000000)
def mhi : ℚ := (284785662161658141006405349193909/5000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (9405145128186672679631128225096789310116515908581537615512780995117060623483717955057782767/26522500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (15053737049501750178137627/1000000000000000000000000)) (.exp (-269690087858373974070449749327745204772755279080316077315289/50000000000000000000000000000000000000000000000000000000000) (56808284338562781097/12500000000000000000000) (4544662747085022487761/1000000000000000000000000) { parts := 6, inner := (-269690087858373974070449749327745204772755279080316077315289/300000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (406989879668559471827111580413/1000000000000000000000000000000), innerHi := (203494939834279735913555790207/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (433591521180714178841079124539451691585276843688404385863562305788083572550931595406648224211/1326125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (15053737049501750178137627/1000000000000000000000000)) (.exp (-6202872020742601403620344234538139709773371418847269778251647/1000000000000000000000000000000000000000000000000000000000000) (126475651955502549161/62500000000000000000000) (2023610431288040786577/1000000000000000000000000) { parts := 7, inner := (-886124574391800200517192033505448529967624488406752825464521/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (412250306363960464430852419449/1000000000000000000000000000000), innerHi := (8245006127279209288617048389/20000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell299
