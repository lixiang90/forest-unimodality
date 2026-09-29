import ForestUnimodality.AnalyticNumericCertificate
import ForestUnimodality.FiniteKernelGraphBudget
import ForestUnimodality.Stage170KernelData.Cell294.Parameters

namespace ForestUnimodality.Stage170KernelData.Cell294
open AnalyticNumericCertificate FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rate : Fin 1 → ℚ := ![(107754504643767711713070558667/1000000000000000000000000000000)]
def R : ℚ := (614337511/400000000)
def D : ℚ := (2365851798699186991869918699187/1000000000000000000000000000000)
def vmax : ℚ := (9840/41209)
def mlo : ℚ := (12436072874311859834063804354361/250000000000000000000000000000)
def mhi : ℚ := (286029676109172776183467500150303/5000000000000000000000000000000)

def budgetExpression_lo : Expr := (.sub (.rat (90698526923903728246980682006977889988713421778018069138593473149437889487715491572952460473/257556250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4006118238175014667490359/250000000000000000000000)) (.exp (-1340042872285270974729801680194387314162488725558585507796787/250000000000000000000000000000000000000000000000000000000000) (4700100022351979491311/1000000000000000000000000) (293756251396998718207/62500000000000000000000) { parts := 6, inner := (-446680957428423658243267226731462438054162908519528502598929/500000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (40927748119009452072245022479/100000000000000000000000000000), innerHi := (409277481190094520722450224791/1000000000000000000000000000000) })))
theorem budgetExpression_lo_checked : budgetExpression_lo.positiveCheck = true := by decide +kernel

theorem budgetExpression_lo_eval : budgetExpression_lo.eval =
    row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  norm_num [budgetExpression_lo, Expr.eval, RationalRow.graphBudget, KernelBudget.budget,
    row, rate, R, D, vmax, mlo, mhi, Fin.sum_univ_succ]

theorem budget_lo_positive : 0 < row.graphBudget (fun i => (rate i : ℝ)) (R * vmax : ℚ) 0 D mlo := by
  rw [← budgetExpression_lo_eval]
  exact budgetExpression_lo.positiveCheck_sound budgetExpression_lo_checked

def budgetExpression_hi : Expr := (.sub (.rat (4151552058399177062116794640742011548100017406867585070592661529363469608364598554750611566871/12877812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.mul (.rat (4006118238175014667490359/250000000000000000000000)) (.exp (-30820986062561232418785438644470908225737240687847466679326101/5000000000000000000000000000000000000000000000000000000000000) (2103406275221614471469/1000000000000000000000000) (210340627522161447147/100000000000000000000000) { parts := 7, inner := (-4402998008937318916969348377781558317962462955406780954189443/5000000000000000000000000000000000000000000000000000000000000), terms := 40, innerLo := (103633570413320338612453998759/250000000000000000000000000000), innerHi := (414534281653281354449815995037/1000000000000000000000000000000) })))
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
end ForestUnimodality.Stage170KernelData.Cell294
