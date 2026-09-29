import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage80KernelData.Cell227.Parameters

namespace ForestUnimodality.Stage80KernelData.Cell227
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(6831344296164892988738223113/40000000000000000000000000000)]
def R : ℚ := (806901209090909090909090909091/500000000000000000000000000000)
def D : ℚ := (587751200888888888888888888889/250000000000000000000000000000)
def vmax : ℚ := (45/196)
def mlo : ℚ := (499390243902439024390243902439/25000000000000000000000000000)
def mhi : ℚ := (3073170731707317073170731707317/125000000000000000000000000000)
def alpha : ℚ := (7262110881818181818181818181819/19600000000000000000000000000000)
def varianceIntercept : ℚ := (0/1)

def budgetExpression_lo : Expr := (.sub (.rat (10523270025179804493644342151492677435294528638208940655909482508294884433860363864863157/30625000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6980909643118560659047489/1000000000000000000000000)) (.exp (-3411506694243321559619880932650443137943995978219786872607/1000000000000000000000000000000000000000000000000000000000) (16495727437264569411921/500000000000000000000000) (32991454874529138823843/1000000000000000000000000) { parts := 4, inner := (-3411506694243321559619880932650443137943995978219786872607/4000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (426187165502795409550822209149/1000000000000000000000000000000), innerHi := (8523743310055908191016444183/20000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, alpha, varianceIntercept, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) alpha varianceIntercept D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (40404386494091566333148263852860012579534109327090402378492931768400267833817309688792227/153125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (6980909643118560659047489/1000000000000000000000000)) (.exp (-20993887349189671136122344200926329413831987934659360617821/5000000000000000000000000000000000000000000000000000000000) (15013920576050867321111/1000000000000000000000000) (1876740072006358415139/125000000000000000000000) { parts := 5, inner := (-20993887349189671136122344200926329413831987934659360617821/25000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (53977011520235551193872160703/125000000000000000000000000000), innerHi := (690905747459015055281563657/1600000000000000000000000000) })))
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
end ForestUnimodality.Stage80KernelData.Cell227
