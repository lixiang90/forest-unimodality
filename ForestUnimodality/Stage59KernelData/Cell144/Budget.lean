import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell144.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell144
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(99002451318928540374764834427/1000000000000000000000000000000)]
def alpha : ℚ := (172249507970063157156463434673/1000000000000000000000000000000)
def D : ℚ := (740014235023605339934576960481/500000000000000000000000000000)
def mlo : ℚ := (8158078332670993950633638009449/500000000000000000000000000000)
def mhi : ℚ := (22074800194286218925243961672627/1000000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha varianceIntercept D m

def budgetExpression_lo : Expr := (.sub (.rat (15755609729320746910801541014316928524120259551076180406976172995400483393287858588679/12500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3057944584798771625600011/500000000000000000000000)) (.exp (-807669752986265792620658442592571677315809734807808346500723/500000000000000000000000000000000000000000000000000000000000) (99411578665762282826861/500000000000000000000000) (198823157331524565653723/1000000000000000000000000) { parts := 2, inner := (-807669752986265792620658442592571677315809734807808346500723/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (87089043777934313257615701/195312500000000000000000000), innerHi := (445895904143023683878992389121/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, varianceIntercept, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (732053834555294061746700745266350861165274946300682247426647869737373351877605962003667/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (3057944584798771625600011/500000000000000000000000)) (.exp (-2185459331609895674150016962309340715810814261403591633129729/1000000000000000000000000000000000000000000000000000000000000) (56213040469791600886923/500000000000000000000000) (112426080939583201773847/1000000000000000000000000) { parts := 3, inner := (-728486443869965224716672320769780238603604753801197211043243/1000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (482638938665992718860157264611/1000000000000000000000000000000), innerHi := (120659734666498179715039316153/250000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell144
