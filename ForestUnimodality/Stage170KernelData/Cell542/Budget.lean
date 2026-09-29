import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell542.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell542
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(156930746776485755458306886889/1000000000000000000000000000000)]
def R : ℚ := (69514686301369863013698630137/50000000000000000000000000000)
def D : ℚ := (62906666332547169811320754717/31250000000000000000000000000)
def vmax : ℚ := (1961/8100)
def mlo : ℚ := (10722754911771359510444054600299/250000000000000000000000000000)
def mhi : ℚ := (567675260034954327023508772957/12500000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (16939828634798191464915432575159365745741572221599560271049594486842217711803095368283603/50625000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4496649007245364870755111/250000000000000000000000)) (.exp (-1682729935805510077669235179020901652411229986606773898579811/250000000000000000000000000000000000000000000000000000000000) (298358699909688729829/250000000000000000000000) (1193434799638754919317/1000000000000000000000000) { parts := 7, inner := (-1682729935805510077669235179020901652411229986606773898579811/1750000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (382296052758478648763199098007/1000000000000000000000000000000), innerHi := (47787006594809831095399887251/125000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (8292264496732883495941297266767142518830096585730894180610547191498620986553991658567261/25312500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4496649007245364870755111/250000000000000000000000)) (.exp (-89085702483821121758959509477576223182084078786502981060773/12500000000000000000000000000000000000000000000000000000000) (200810162809650179193/250000000000000000000000) (803240651238600716773/1000000000000000000000000) { parts := 8, inner := (-89085702483821121758959509477576223182084078786502981060773/100000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (25643997583800218912750932651/62500000000000000000000000000), innerHi := (410303961340803502604014922417/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell542
