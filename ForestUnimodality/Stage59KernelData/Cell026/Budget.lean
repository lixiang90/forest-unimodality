import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell026.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell026
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(121562321085637518510750523287/1000000000000000000000000000000)]
def alpha : ℚ := (19383985775840000000000000000003311/88711200000000000000000000000000000)
def D : ℚ := (351239627/200000000)
def mlo : ℚ := (2212624584717607973421926910299/125000000000000000000000000000)
def mhi : ℚ := (27657807308970099667774086378737/1000000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (3291329350489642087878276439088298206635130353786923593993611757365984853126030184215073229/2310187500000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1150466096732425391735433/100000000000000000000000)) (.exp (-268971780209417233648371589731368366902587755357081359632813/125000000000000000000000000000000000000000000000000000000000) (116277669960068095036137/1000000000000000000000000) (58138834980034047518069/500000000000000000000000) { parts := 3, inner := (-89657260069805744549457196577122788967529251785693786544271/125000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (30505545177422346716692525809/62500000000000000000000000000), innerHi := (97617744567751509493416082589/200000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (2244242306890037134983025327012603988829871563871312277004460671159515075437559054982786193/4620375000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (1150466096732425391735433/100000000000000000000000)) (.exp (-3362147252617715420604644871642043805121804123204261620148519/1000000000000000000000000000000000000000000000000000000000000) (34660753588579750170129/1000000000000000000000000) (3466075358857975017013/100000000000000000000000) { parts := 4, inner := (-3362147252617715420604644871642043805121804123204261620148519/4000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (21573941886636302582081934671/50000000000000000000000000000), innerHi := (431478837732726051641638693421/1000000000000000000000000000000) })))
theorem budgetExpression_hi_checked : budgetExpression_hi.positiveCheck=true := by decide +kernel

theorem budgetExpression_hi_eval : budgetExpression_hi.eval = budget mhi := by
  norm_num [budgetExpression_hi, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
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
    row.A row.B row.dδ row.dM alpha 0 D
    (fun i => (row.price i : ℝ)) (fun i => (rate i : ℝ))
    (fun j => (row.fixedPrice j : ℝ)) (fun j => (countBound j : ℝ))
    (by norm_num [mlo, mhi]) hdM hT budget_lo_positive budget_hi_positive hm

#print axioms budget_lo_positive
#print axioms budget_hi_positive
#print axioms budget_positive
end ForestUnimodality.Stage59KernelData.Cell026
