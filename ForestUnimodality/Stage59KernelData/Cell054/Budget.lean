import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelSupportGraphBudget
import ForestUnimodality.Stage59KernelData.Cell054.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell054
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(46241962238200446071680986243/500000000000000000000000000000)]
def alpha : ℚ := (262478798612674637904000000000027711/1445824576000000000000000000000000000)
def D : ℚ := (1637487884127659574468085106383/1000000000000000000000000000000)
def mlo : ℚ := (2186884269784562087257767673487/125000000000000000000000000000)
def mhi : ℚ := (40135758363104904189671971419291/2000000000000000000000000000000)

noncomputable def budget (m : ℝ) : ℝ :=
  row.graphBudgetWithCounts (fun i => (rate i : ℝ)) (fun j => (countBound j : ℝ)) alpha 0 D m

def budgetExpression_lo : Expr := (.sub (.rat (798369069207163427293125815206824787917397169914857584471317156222814417157501394202197401947/806821750000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4900313230193241942345139/1000000000000000000000000)) (.exp (-101125819822692276795439411319165733833489185400111762839341/62500000000000000000000000000000000000000000000000000000000) (2478653643672418922991/12500000000000000000000) (198292291493793513839281/1000000000000000000000000) { parts := 2, inner := (-101125819822692276795439411319165733833489185400111762839341/125000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (445300226244938611123999164011/1000000000000000000000000000000), innerHi := (111325056561234652780999791003/250000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck=true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval = budget mlo := by
  norm_num [budgetExpression_lo, Expr.eval, budget, RationalRow.graphBudgetWithCounts,
    KernelBudget.budget, row, rate, countBound, alpha, D, mlo, mhi, Fin.sum_univ_succ]
  ring

theorem budget_lo_positive : 0 < budget mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (70824151900532178494637317491309531949849378574234179203673874094948163444203315821328988965413/90364036000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4900313230193241942345139/1000000000000000000000000)) (.exp (-1855956222628234727069240960681167510702078849774887355813713/1000000000000000000000000000000000000000000000000000000000000) (156303410335412273251087/1000000000000000000000000) (9768963145963267078193/62500000000000000000000) { parts := 2, inner := (-1855956222628234727069240960681167510702078849774887355813713/2000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (98838065268211655126268647391/250000000000000000000000000000), innerHi := (79070452214569324101014917913/200000000000000000000000000000) })))
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
end ForestUnimodality.Stage59KernelData.Cell054
