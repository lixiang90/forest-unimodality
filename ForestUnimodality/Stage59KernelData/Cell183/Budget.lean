import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell183.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell183
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(101130400797699006188743945419/1000000000000000000000000000000)]
def alpha : ℚ := (34980653505153453001788953853/200000000000000000000000000000)
def D : ℚ := (752707711865398072042527859299/500000000000000000000000000000)
def mlo : ℚ := (16973458349865307912377054315367/1000000000000000000000000000000)
def mhi : ℚ := (27346127341449662747718587508091/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (793383949491359758204994197488292661394995787237498779231668150474428464513865195483/400000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (263250018138065478012777/25000000000000000000000)) (.exp (-1716532645844929392575450305680549663991589999449627460953773/1000000000000000000000000000000000000000000000000000000000000) (179688111324066280338679/1000000000000000000000000) (4492202783101657008467/25000000000000000000000) { parts := 2, inner := (-1716532645844929392575450305680549663991589999449627460953773/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (211948172511622685339584039421/500000000000000000000000000000), innerHi := (423896345023245370679168078843/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (301653746838461469270658222201201096279981451002552048698944702672462147579269348959/400000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (263250018138065478012777/25000000000000000000000)) (.exp (-2765524818305719576927114381374190811319562304944902924885129/1000000000000000000000000000000000000000000000000000000000000) (31471528504812435653759/500000000000000000000000) (62943057009624871307519/1000000000000000000000000) { parts := 3, inner := (-921841606101906525642371460458063603773187434981634308295043/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (198892900681665999730060632299/500000000000000000000000000000), innerHi := (397785801363331999460121264599/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell183
