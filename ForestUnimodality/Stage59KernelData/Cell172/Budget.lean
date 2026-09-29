import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell172.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell172
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(20139471957035076117677562067/200000000000000000000000000000)]
def alpha : ℚ := (34719217714415919907099978821/200000000000000000000000000000)
def D : ℚ := (1506871204797117539853782181537/1000000000000000000000000000000)
def mlo : ℚ := (4255583828102912072377721232683/250000000000000000000000000000)
def mhi : ℚ := (27424873558885433355323092388401/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (238010459801167313260309001584225622759962625493458005130871318621440704678558623297/125000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1018271683110954484163813/100000000000000000000000)) (.exp (-85705211166890575550829138883935365581261475535077481435761/50000000000000000000000000000000000000000000000000000000000) (90062500119300334337327/500000000000000000000000) (36025000047720133734931/200000000000000000000000) { parts := 2, inner := (-85705211166890575550829138883935365581261475535077481435761/100000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (424411357339316107838649190649/1000000000000000000000000000000), innerHi := (8488227146786322156772983813/20000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (356682830935649595762162890170233114317772300018617084638618206574553275973277480659/500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1018271683110954484163813/100000000000000000000000)) (.exp (-552322471964405931327565561696461167372597822850433948384867/200000000000000000000000000000000000000000000000000000000000) (15797450370252969575549/250000000000000000000000) (63189801481011878302197/1000000000000000000000000) { parts := 3, inner := (-552322471964405931327565561696461167372597822850433948384867/600000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (199152456634065174376905535209/500000000000000000000000000000), innerHi := (398304913268130348753811070419/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell172
