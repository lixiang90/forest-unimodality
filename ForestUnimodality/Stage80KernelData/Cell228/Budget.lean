import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage80KernelData.Cell228.Parameters

namespace ForestUnimodality.Stage80KernelData.Cell228
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(17700070439509760042206000723/100000000000000000000000000000)]
def R : ℚ := (1674588520930232558139534883721/1000000000000000000000000000000)
def D : ℚ := (2334529135219512195121951219513/1000000000000000000000000000000)
def vmax : ℚ := (902/3969)
def mlo : ℚ := (1233433734939759036144578313253/62500000000000000000000000000)
def mhi : ℚ := (12144578313253012048192771084337/500000000000000000000000000000)
def alpha : ℚ := (755239422939534883720930232558171/1984500000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.rat (2740124619409172578001730290527349261863882258745033713423373124223872064037132574351691649/8268750000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4026477868949335792159161/625000000000000000000000)) (.exp (-21831863990901345594226979807435027709994704701686238481919/6250000000000000000000000000000000000000000000000000000000) (15203259716272626703021/500000000000000000000000) (30406519432545253406043/1000000000000000000000000) { parts := 4, inner := (-21831863990901345594226979807435027709994704701686238481919/25000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (417581911119731273685402723857/1000000000000000000000000000000), innerHi := (208790955559865636842701361929/500000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (18011409298840550660368313893504814790279650789448214185484376762649571655114765412313714807/66150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4026477868949335792159161/625000000000000000000000)) (.exp (-214959891602720941235465647334740803589846436348900915975651/50000000000000000000000000000000000000000000000000000000000) (1697430955247407126943/125000000000000000000000) (2715889528395851403109/200000000000000000000000) { parts := 5, inner := (-214959891602720941235465647334740803589846436348900915975651/250000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (3306484196684024880135334933/7812500000000000000000000000), innerHi := (16929199087022207386292914857/40000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck = true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  norm_num [budgetExpression_hi, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

theorem budget_hi_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mhi := by
  rw [← budgetExpression_hi_eval]
  exact budgetExpression_hi.positiveCheck_sound budgetExpression_hi_checked

theorem budget_positive {m : ℝ} (hm : m ∈ Set.Icc (mlo : ℝ) (mhi : ℝ)) :
    0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D m := by
  have hs := row.signCheck_sound row_checked
  have hdM : (0 : ℝ) ≤ row.dM := by norm_num [row]
  have hT : ∀ i ∈ row.terms, (0 : ℝ) ≤ row.price i := by
    intro i hi
    exact hs.price i hi
  exact KernelBudget.budget_pos_of_endpoints row.terms (∅ : Finset ℤ)
    row.A row.B row.dδ row.dM alpha varianceIntercept D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ)) (fun _ => 0) (fun _ => 0)
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage80KernelData.Cell228
