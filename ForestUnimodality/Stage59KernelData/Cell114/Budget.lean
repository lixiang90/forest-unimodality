import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell114.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell114
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(48493578397134205329040801101/500000000000000000000000000000)]
def alpha : ℚ := (175470783620868896578239138793/1000000000000000000000000000000)
def D : ℚ := (1464643660914972802748353850559/1000000000000000000000000000000)
def mlo : ℚ := (4168269230769230769230769230769/250000000000000000000000000000)
def mhi : ℚ := (22067307692307692307692307692307/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (28093466549630571757944162504669505679452056157306927834049248093117891437369495067653/25000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2809358568508294240473333/500000000000000000000000)) (.exp (-202134290722669980866722954589253232251139122875693298276669/125000000000000000000000000000000000000000000000000000000000) (3101227093685284838183/15625000000000000000000) (198478533995858229643713/1000000000000000000000000) { parts := 2, inner := (-202134290722669980866722954589253232251139122875693298276669/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (22275464865848379733321474283/50000000000000000000000000000), innerHi := (445509297316967594666429485661/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (167362744331479058908197312349390817037725754562257747104692030854819079759144114995291/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (2809358568508294240473333/500000000000000000000000)) (.exp (-1070122715590605781059121524296072196753417368627079894830007/500000000000000000000000000000000000000000000000000000000000) (117625970397947117536961/1000000000000000000000000) (58812985198973558768481/500000000000000000000000) { parts := 3, inner := (-356707571863535260353040508098690732251139122875693298276669/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (489968025676960330373800789713/1000000000000000000000000000000), innerHi := (244984012838480165186900394857/500000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell114
